import PetersenSignalCut

open PetersenWordCost PetersenSignalCut

namespace PetersenForwardSearch
variable {w : Nat}
abbrev B := BitVec w

def cb (W : List (BitVec w)) (a : BitVec w) : Bool :=
  (0::W).contains a || (0::W).contains (~~~a)

theorem cb_spec {W : List (BitVec w)} {a : BitVec w} : cb W a = true ↔ Covered W a := by
  simp [cb,Covered]

private theorem covNeg {W : List (BitVec w)} {a : BitVec w} (h : Covered W a) : Covered W (~~~a) := by
  rcases h with h|h
  · exact Or.inr (by simpa using h)
  · exact Or.inl h

private theorem wcov {W : List (BitVec w)} {a : BitVec w} (h : a ∈ W) : Covered W a :=
  Or.inl (List.mem_cons_of_mem _ h)
private theorem wzero (W : List (BitVec w)) : Covered W 0 := Or.inl (by simp)

def Sim (small big : List (BitVec w)) : Prop := ∀ x ∈ small, Covered big x

private theorem subsume {W V : List (BitVec w)} (s : Sim W V) {x} (hx : Covered W x) : Covered V x := by
  rcases hx with h|h
  · rcases List.mem_cons.mp h with rfl|h
    · exact wzero V
    · exact s _ h
  · rcases List.mem_cons.mp h with hz|h
    · have z := covNeg (W:=V) (a := ~~~x) (hz ▸ wzero V)
      simpa using z
    · simpa using covNeg (s _ h)

private theorem widen {W : List (BitVec w)} {a : BitVec w} (g : BitVec w) (h : Covered W a) :
    Covered (g::W) a := by
  apply subsume (W:=W) _ h
  exact fun x hx => wcov (List.mem_cons_of_mem _ hx)

theorem reject_sim {W V : List (BitVec w)} {t : BitVec w} (d : Nat) (s : Sim W V) :
    Reject t d V → Reject t d W := by
  induction d generalizing W V with
  | zero => intro h ht; exact h (subsume s ht)
  | succ d ih =>
    intro h a b ha hb op
    apply ih (V:=gate op a b :: V) _ (h a b (subsume s ha) (subsume s hb) op)
    intro x hx
    rcases List.mem_cons.mp hx with rfl|h
    · exact wcov (List.mem_cons_self ..)
    · exact widen _ (s _ h)

theorem reject_lower {W : List (BitVec w)} {t} {k d : Nat} (le : k ≤ d) :
    Reject t d W → Reject t k W := by
  induction le with
  | refl => exact id
  | step le ih =>
    intro h
    exact ih (reject_sim _ (fun x hx => wcov (List.mem_cons_of_mem _ hx)) (h 0 0 (wzero W) (wzero W) false))

private theorem reject_of_tail {I W : List (BitVec w)} {k : Nat} {t : BitVec w}
    (r : Packed I k W) (d : Nat)
    (h : ∀ S, Packed I (k+d) S → ¬Covered S t) : Reject t d W := by
  induction d generalizing k W with
  | zero => exact h W r
  | succ d ih =>
    intro a b ha hb op
    apply ih (Packed.step r ha hb op)
    intro S rs
    apply h S
    convert rs using 1; omega

def signs (W : List (BitVec w)) : List (BitVec w) :=
  (0::W) ++ (0::W).map (fun a => ~~~a)

private theorem mem_signs {W : List (BitVec w)} {a : BitVec w} (h : Covered W a) : a ∈ signs W := by
  apply List.mem_append.mpr
  rcases h with h|h
  · exact Or.inl h
  · exact Or.inr (List.mem_map.mpr ⟨~~~a,h,by simp⟩)

/-- Every U2 truth table has an AND representative up to the free output sign. -/
def steps (W : List (BitVec w)) : List (BitVec w) :=
  (((signs W).product (signs W)).map (fun p => p.1 &&& p.2)).eraseDups

private theorem and_mem {W : List (BitVec w)} {a b : BitVec w} (ha : Covered W a) (hb : Covered W b) :
    a &&& b ∈ steps W := by
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨(a,b),List.mem_product.mpr ⟨mem_signs ha,mem_signs hb⟩,rfl⟩

private theorem step_rep {W : List (BitVec w)} {a b : BitVec w} (ha : Covered W a) (hb : Covered W b) (op : Bool) :
    ∃ v ∈ steps W, ∀ T : List (BitVec w), Covered (v::T) (gate op a b) := by
  cases op with
  | false => exact ⟨_, and_mem ha hb, fun _ => wcov (List.mem_cons_self ..)⟩
  | true =>
    refine ⟨_,and_mem (covNeg ha) (covNeg hb),?_⟩
    intro T
    apply Or.inr
    simp [gate,BitVec.not_or]

/-- A cache entry can be built only from a checked proof for this target. -/
structure Entry (t : BitVec w) where
  fuel : Nat
  wires : List (BitVec w)
  valid : Reject t fuel wires

def cacheHit {t : BitVec w} (cache : List (Entry t)) (k : Nat) (W : List (BitVec w)) : Bool :=
  cache.any fun e => decide (k ≤ e.fuel) && W.all (cb e.wires)

theorem cacheHit_sound {t : BitVec w} {cache : List (Entry t)} {k : Nat} {W : List (BitVec w)}
    (h : cacheHit cache k W = true) : Reject t k W := by
  obtain ⟨e,_,eq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at eq
  exact reject_sim k (fun x hx => cb_spec.mp (eq.2 x hx)) (reject_lower eq.1 e.valid)

/-- Search depth-first, retain one prefix per call, and skip previously available gate
outputs. A failed heuristic or absent cache entry merely causes further exploration. -/
def search (t : BitVec w) (probes : Pairs w) (cache : List (Entry t)) :
    Nat → List (BitVec w) → Bool
  | 0, W => !cb W t
  | k+1, W =>
    if cacheHit cache (k+1) W then true else
    if cb W t then false else
    if W.length > k+2 && decide (k+2 < (forcedSet W t probes).card) then true else
      search t probes cache k W &&
      (steps W).all fun v => cb W v || search t probes cache k (v::W)

theorem search_sound {t : BitVec w} (probes : Pairs w) (cache : List (Entry t)) :
    ∀ k W, search t probes cache k W = true → Reject t k W := by
  intro k
  induction k with
  | zero =>
    intro W h hit
    have := cb_spec.mpr hit
    simp [search,this] at h
  | succ k ih =>
    intro W h
    simp only [search] at h
    split at h
    next hh => exact cacheHit_sound hh
    split at h
    next => contradiction
    split at h
    next hh =>
      have ff := (Bool.and_eq_true_iff.mp hh).2
      apply reject_of_tail (Packed.start (I:=W)) (k+1)
      intro S r
      exact cut probes r (by simpa using of_decide_eq_true ff)
    have hh := Bool.and_eq_true_iff.mp h
    intro a b ha hb op
    obtain ⟨v,hv,cover⟩ := step_rep ha hb op
    have opt := List.all_eq_true.mp hh.2 v hv
    rcases Bool.or_eq_true_iff.mp opt with seen|explored
    · apply reject_sim k _ (ih _ hh.1)
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · apply subsume (W:=v::W) _ (cover W)
        intro z hz; rcases List.mem_cons.mp hz with rfl|hz
        · exact cb_spec.mp seen
        · exact wcov hz
      · exact wcov hx
    · apply reject_sim k _ (ih _ explored)
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact cover W
      · exact wcov (List.mem_cons_of_mem _ hx)

end PetersenForwardSearch
