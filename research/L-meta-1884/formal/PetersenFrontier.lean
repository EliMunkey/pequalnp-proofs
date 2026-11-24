import PetersenPhysicalBoundary
import Mathlib.Data.Finset.Card

open PetersenSignedBridge

namespace PetersenFrontier

variable {α : Type*} [DecidableEq α]

/-- A fresh straight-line prefix retains its entire wire environment. -/
inductive Prefix (gate : α → α → α → Prop) (inputs : Finset α) :
    Nat → Finset α → Prop where
  | start : Prefix gate inputs 0 inputs
  | add {k W a b o} : Prefix gate inputs k W → a ∈ W → b ∈ W → a ≠ b →
      o ∉ W → gate a b o → Prefix gate inputs (k+1) (insert o W)

/-- An operand costs one fan-out credit precisely when it remains live after use. -/
def credit (a b : α) (keep : Finset α) : Nat :=
  (if a ∈ keep then 1 else 0) + (if b ∈ keep then 1 else 0)

/-- From the source frontier, consume exactly the two named operands except any
also needed in `keep`. The gate emits one new live signal. -/
inductive Trace (gate : α → α → α → Prop) (inputs : Finset α) :
    Nat → Nat → Finset α → Prop where
  | start : Trace gate inputs 0 0 inputs
  | step {m c keep a b o} :
      Trace gate inputs m c (insert a (insert b keep)) →
      a ≠ b → o ∉ insert a (insert b keep) → gate a b o →
      Trace gate inputs (m+1) (c+credit a b keep) (insert o keep)

/-- Backwards slicing chooses the last use of each operand; no liveness
assumption or preselected gate schedule is required of the source prefix. -/
theorem Prefix.schedule {gate : α → α → α → Prop} {I W k}
    (run : Prefix gate I k W) (need : Finset α) (covered : need ⊆ W) :
    ∃ inputs ⊆ I, ∃ m ≤ k, ∃ c, Trace gate inputs m c need := by
  induction run generalizing need with
  | start => exact ⟨need,covered,0,le_rfl,0,Trace.start⟩
  | @add k W a b o _ ha hb hab fresh g ih =>
    by_cases used : o ∈ need
    · let keep := need.erase o
      have subset : keep ⊆ W := by
        intro x hx
        have h := Finset.mem_erase.mp hx
        exact (Finset.mem_insert.mp (covered h.2)).resolve_left h.1
      have cov : insert a (insert b keep) ⊆ W :=
        Finset.insert_subset ha (Finset.insert_subset hb subset)
      obtain ⟨ins,hi,m,hm,c,t⟩ := ih _ cov
      have hnew : o ∉ insert a (insert b keep) := fun h => fresh (cov h)
      have step := Trace.step t hab hnew g
      have eq : insert o keep = need := Finset.insert_erase used
      exact ⟨ins,hi,m+1,by omega,c+credit a b keep,eq ▸ step⟩
    · have cov : need ⊆ W := by
        intro x hx
        rcases Finset.mem_insert.mp (covered hx) with eq|h
        · exact False.elim (used (eq ▸ hx))
        · exact h
      obtain ⟨ins,hi,m,hm,c,t⟩ := ih _ cov
      exact ⟨ins,hi,m,by omega,c,t⟩

theorem Prefix.inputs {gate : α → α → α → Prop} {I W k} (r : Prefix gate I k W) : I ⊆ W := by
  induction r with
  | start => exact fun _ h => h
  | add _ _ _ _ _ _ ih => exact fun _ h => Finset.mem_insert_of_mem (ih h)

theorem Prefix.no_input_output {gate : α → α → α → Prop} {I W k} (r : Prefix gate I k W) :
    Prefix (fun a b o => o ∉ I ∧ gate a b o) I k W := by
  induction r with
  | start => exact Prefix.start
  | add prior ha hb ne new g ih =>
    exact Prefix.add ih ha hb ne new ⟨fun h => new (prior.inputs h),g⟩

/-- Equality of live-count, gate-count and fan-out credits on every prefix. -/
theorem Trace.account {gate : α → α → α → Prop} {I W m c} (t : Trace gate I m c W) :
    W.card + m = I.card + c := by
  induction t with
  | start => simp
  | @step m c keep a b o _ hab hnew _ ih =>
    have hao : o ∉ keep := fun h => hnew (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    by_cases ha : a ∈ keep <;> by_cases hb : b ∈ keep <;>
      simp [credit,ha,hb,hab,hao,Finset.card_insert_of_notMem] at * <;> omega

/-- A single-output cone from n demanded inputs uses m−n+1 credits. -/
theorem Trace.sink {gate : α → α → α → Prop} {I m c} {out : α}
    (t : Trace gate I m c {out}) : m+1 = I.card+c := by
  have h := t.account
  simpa [Nat.add_comm] using h


section Physical
variable {Ω : Type}
noncomputable local instance : DecidableEq (Func Ω) := Classical.decEq _

/-- Physical gates use precisely the polarities actually available at their sources. -/
def physical (a b o : Func Ω) : Prop :=
  o = (fun x => a x && b x) ∨ o = (fun x => a x || b x)

theorem fresh_prefix {init W : List (Func Ω)} {k} (f : Fresh init k W) :
    Prefix physical init.toFinset k W.toFinset := by
  induction f with
  | start => exact Prefix.start
  | @and k W a b _ ha hb hf ih =>
    have distinct : a ≠ b := by
      rintro rfl
      have hx : (fun x => a x && a x) = a := by funext x; simp
      apply hf
      rw [hx]
      exact Av.wire ha
    rw [List.toFinset_cons]
    exact Prefix.add ih (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb) distinct
      (fun hh => hf (Av.wire (List.mem_toFinset.mp hh))) (Or.inl rfl)
  | @or k W a b _ ha hb hf ih =>
    have distinct : a ≠ b := by
      rintro rfl
      have hx : (fun x => a x || a x) = a := by funext x; simp
      apply hf
      rw [hx]
      exact Av.wire ha
    rw [List.toFinset_cons]
    exact Prefix.add ih (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb) distinct
      (fun hh => hf (Av.wire (List.mem_toFinset.mp hh))) (Or.inr rfl)

/-- Every requested output of the physical Fresh circuit has an exact last-use
schedule from its actually demanded raw inputs, with gates and credits counted. -/
theorem fresh_schedule {init W : List (Func Ω)} {k} (f : Fresh init k W)
    {out : Func Ω} (ho : out ∈ W) :
    ∃ I ⊆ init.toFinset, ∃ m ≤ k, ∃ c,
      Trace physical I m c {out} ∧ m+1 = I.card+c := by
  obtain ⟨I,hI,m,hm,c,tr⟩ := (fresh_prefix f).schedule {out}
    (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr ho))
  exact ⟨I,hI,m,hm,c,tr,tr.sink⟩

end Physical

section Normalized
variable {Ω : Type}
noncomputable local instance : DecidableEq (Func Ω) := Classical.decEq _

def flip (f : Func Ω) : Func Ω := fun x => !(f x)
def bin (isOr : Bool) (a b : Func Ω) : Func Ω :=
  fun x => if isOr then a x || b x else a x && b x
def negRelated (a b : Func Ω) : Prop := a = b ∨ a = flip b
def nonconstant (a : Func Ω) : Prop := a ≠ (fun _ => false) ∧ a ≠ (fun _ => true)

theorem fresh_inputs {W : List (Func Ω)} {a b} (op : Bool) (avA : Av W a) (avB : Av W b)
    (new : ¬ Av W (bin op a b)) :
    nonconstant a ∧ nonconstant b ∧ ¬ negRelated a b ∧ nonconstant (bin op a b) := by
  have z : Av W (fun _ => false) := Av.zero
  have u : Av W (fun _ => true) := Av.one
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_,⟨fun e => new (e ▸ z), fun e => new (e ▸ u)⟩⟩
  · rintro rfl; apply new; cases op
    · convert z using 1 <;> funext x <;> simp [bin,flip]
    · convert avB using 1 <;> funext x <;> simp [bin,flip]
  · rintro rfl; apply new; cases op
    · convert avB using 1 <;> funext x <;> simp [bin,flip]
    · convert u using 1 <;> funext x <;> simp [bin,flip]
  · rintro rfl; apply new; cases op
    · convert z using 1 <;> funext x <;> simp [bin,flip]
    · convert avA using 1 <;> funext x <;> simp [bin,flip]
  · rintro rfl; apply new; cases op
    · convert avA using 1 <;> funext x <;> simp [bin,flip]
    · convert u using 1 <;> funext x <;> simp [bin,flip]
  · rintro (rfl|rfl) <;> apply new
    · cases op
      · convert avA using 1 <;> funext x <;> simp [bin,flip]
      · convert avA using 1 <;> funext x <;> simp [bin,flip]
    · cases op
      · convert z using 1 <;> funext x <;> simp [bin,flip]
      · convert u using 1 <;> funext x <;> simp [bin,flip]

theorem keys_related (key : Func Ω → Func Ω) (sign : ∀ a, negRelated (key a) a) {a b}
    (h : key a = key b) : negRelated a b := by
  have fl (f : Func Ω) : flip (flip f) = f := by funext x; simp [flip]
  rcases sign a with e|e <;> rcases sign b with t|t
  · exact Or.inl (e.symm.trans (h.trans t))
  · exact Or.inr (e.symm.trans (h.trans t))
  · right; have q := congrArg flip (e.symm.trans (h.trans t)); simpa only [fl] using q
  · left; have q := congrArg flip (e.symm.trans (h.trans t)); simpa only [fl] using q

theorem av_related {W : List (Func Ω)} {a b} (h : negRelated a b) (mem : b ∈ W) : Av W a := by
  rcases h with rfl|rfl
  · exact Av.wire mem
  · exact Av.neg (Av.wire mem)

theorem key_hot (key : Func Ω → Func Ω) (sign : ∀ f, negRelated (key f) f) {f}
    (h : nonconstant f) : nonconstant (key f) := by
  rcases sign f with e|e
  · simpa only [e] using h
  · rw [e]
    constructor
    · intro eq; apply h.2; funext x; have v := congrFun eq x; simpa [flip] using v
    · intro eq; apply h.1; funext x; have v := congrFun eq x; simpa [flip] using v

/-- A physical gate keeps the semantic polarity of its operands. Only the
chosen key may identify a source with its complementary primary. -/
def keyedGate (key : Func Ω → Func Ω) (a b o : Func Ω) : Prop :=
  ∃ p q j, key p = a ∧ key q = b ∧ key (bin j p q) = o ∧ nonconstant o

/-- Compile fresh gates from only the nonconstant raw signals. Normalization
can identify complementary physical input rails without double-counting them. -/
theorem fresh_keyed_prefix (key : Func Ω → Func Ω) (sign : ∀ f, negRelated (key f) f)
    {init W : List (Func Ω)} {k} (f : Fresh init k W) (I : Finset (Func Ω))
    (coverage : ∀ p ∈ init, nonconstant p → key p ∈ I)
    (real : ∀ y ∈ I, ∃ p ∈ init, key p = y) :
    ∃ S, Prefix (keyedGate key) I k S ∧
      (∀ p ∈ W, nonconstant p → key p ∈ S) ∧
      (∀ y ∈ S, ∃ p ∈ W, key p = y) := by
  have add {k W S} {a b : Func Ω} (j : Bool)
      (ha : a ∈ W) (hb : b ∈ W) (new : ¬ Av W (bin j a b))
      (r : Prefix (keyedGate key) I k S)
      (cov : ∀ p ∈ W, nonconstant p → key p ∈ S)
      (exactly : ∀ y ∈ S, ∃ p ∈ W, key p = y) :
      ∃ T, Prefix (keyedGate key) I (k+1) T ∧
        (∀ p ∈ bin j a b :: W, nonconstant p → key p ∈ T) ∧
        (∀ y ∈ T, ∃ p ∈ bin j a b :: W, key p = y) := by
    obtain ⟨aa,bb,nh,hot⟩ := fresh_inputs j (Av.wire ha) (Av.wire hb) new
    have ne : key a ≠ key b := fun h => nh (keys_related key sign h)
    have fresh : key (bin j a b) ∉ S := by
      intro hit
      obtain ⟨p,hp,eq⟩ := exactly _ hit
      exact new (av_related (keys_related key sign eq.symm) hp)
    refine ⟨insert (key (bin j a b)) S,
      Prefix.add r (cov _ ha aa) (cov _ hb bb) ne fresh ⟨a,b,j,rfl,rfl,rfl,key_hot key sign hot⟩,?_,?_⟩
    · intro p hp nc
      rcases List.mem_cons.mp hp with rfl|h
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (cov _ h nc)
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl|h
      · exact ⟨_,List.mem_cons_self ..,rfl⟩
      · obtain ⟨p,hp,eq⟩ := exactly _ h
        exact ⟨p,List.mem_cons_of_mem _ hp,eq⟩
  induction f with
  | start => exact ⟨I,Prefix.start,coverage,real⟩
  | and _ ha hb hf ih =>
    obtain ⟨S,r,cov,ex⟩ := ih
    exact add false ha hb hf r cov ex
  | or _ ha hb hf ih =>
    obtain ⟨S,r,cov,ex⟩ := ih
    exact add true ha hb hf r cov ex

end Normalized

section Projection

variable {Ω : Type}
noncomputable local instance : DecidableEq (Func Ω) := Classical.decEq _

/-- Agreement on the starting inputs is preserved at every live frontier. -/
theorem Trace.agree {gate : Func Ω → Func Ω → Func Ω → Prop} {I W m c}
    (tr : Trace gate I m c W) (x y : Ω)
    (step : ∀ a b o, gate a b o → a x = a y → b x = b y → o x = o y)
    (initial : ∀ a ∈ I, a x = a y) : ∀ a ∈ W, a x = a y := by
  induction tr with
  | start => exact initial
  | @step m c keep a b o _ _ _ g ih =>
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|h
    · exact step _ _ _ g (ih _ (Finset.mem_insert_self ..))
        (ih _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))
    · exact ih _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))

theorem keyed_stable (key : Func Ω → Func Ω) (sign : ∀ f, negRelated (key f) f)
    (x y : Ω) {a b o} (g : keyedGate key a b o)
    (ha : a x = a y) (hb : b x = b y) : o x = o y := by
  obtain ⟨p,q,j,rfl,rfl,rfl,_⟩ := g
  have d (f : Func Ω) : (key f x = key f y) ↔ f x = f y := by
    rcases sign f with eq|eq <;> rw [eq] <;> simp [flip]
  apply (d _).mpr
  simp [bin,(d p).mp ha,(d q).mp hb]

def vertex (i : Fin 10) : Func PInput := fun x => x i
def negZero : Func PInput := flip (vertex 0)

/-- Only the two originally free polarities of vertex zero share a register. -/
noncomputable def physicalKey (f : Func PInput) : Func PInput :=
  if f = negZero then vertex 0 else f

theorem physicalSign (f : Func PInput) : negRelated (physicalKey f) f := by
  by_cases e : f = negZero
  · subst f; right; simp only [physicalKey,if_pos rfl,negZero]; funext x; simp [flip]
  · left; simp [physicalKey,e]

theorem projected_vertex (i : Fin 10) : physicalKey (vertex i) = vertex i := by
  have h : vertex i ≠ negZero := by
    intro e
    have := congrFun e (fun _ => false)
    contradiction
  simp [physicalKey,h]

theorem rails_cover (f : Func PInput) (hr : f ∈ rails) (nc : nonconstant f) :
    physicalKey f ∈ base.toFinset := by
  rcases List.mem_cons.mp hr with rfl|hr
  · exact False.elim (nc.1 rfl)
  rcases List.mem_cons.mp hr with rfl|hr
  · exact False.elim (nc.2 rfl)
  rcases List.mem_cons.mp hr with rfl|hr
  · change physicalKey negZero ∈ base.toFinset
    simp [physicalKey]
    exact List.mem_ofFn.mpr ⟨0,rfl⟩
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact (projected_vertex i) ▸ (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))

theorem rails_real (v : Func PInput) (hv : v ∈ base.toFinset) :
    ∃ f ∈ rails, physicalKey f = v := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hv)
  refine ⟨vertex i,?_,projected_vertex i⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_ofFn.mpr ⟨i,rfl⟩)))

def mate : Fin 10 → Fin 10 := ![1,0,1,4,3,0,1,2,3,4]
def single (i : Fin 10) : PInput := fun j => decide (j = mate i)
def doubled (i : Fin 10) : PInput := fun j => decide (j = mate i ∨ j = i)

theorem pivots (i : Fin 10) :
    PetersenTarget (single i) = false ∧ PetersenTarget (doubled i) = true := by
  revert i; decide

theorem targetKey : physicalKey PetersenTarget = PetersenTarget := by
  have h : PetersenTarget ≠ negZero := by
    intro e
    have eq := congrFun e (fun _ => false)
    contradiction
  simp [physicalKey,h]

theorem targetHot : nonconstant PetersenTarget := by
  constructor
  · intro e
    have h := congrFun e (doubled 0)
    rw [(pivots 0).2] at h
    contradiction
  · intro e
    have h := congrFun e (single 0)
    rw [(pivots 0).1] at h
    contradiction

theorem demanded {gate : Func PInput → Func PInput → Func PInput → Prop}
    (stable : ∀ x y a b o, gate a b o → a x = a y → b x = b y → o x = o y)
    {I m c} (hi : I ⊆ base.toFinset) (t : Trace gate I m c {PetersenTarget}) :
    I = base.toFinset := by
  apply Finset.Subset.antisymm hi
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hf)
  by_contra miss
  have agree : ∀ a ∈ I, a (single i) = a (doubled i) := by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (hi ha))
    have ne : j ≠ i := by rintro rfl; exact miss ha
    simp [single,doubled,ne]
  have eq := t.agree (single i) (doubled i) (stable _ _) agree _ (Finset.mem_singleton_self _)
  rw [(pivots i).1,(pivots i).2] at eq
  contradiction

theorem ten_inputs : base.toFinset.card = 10 := by
  have inj : Function.Injective (vertex : Fin 10 → Func PInput) := by
    intro i j eq
    have e := congrFun eq (fun h => decide (h=i))
    simpa [vertex,eq_comm] using e
  have nodup : base.Nodup := List.nodup_ofFn_ofInjective inj
  rw [List.toFinset_card_of_nodup nodup]
  exact List.length_ofFn

/-- Source-level coverage with exactly the ten primary registers. Each
hypothetical Fresh circuit for the project target has a searched last-use
path; the binary target computation may cost fewer gates after slicing. -/
theorem petersen_fresh_frontier {W : List (Func PInput)} {k}
    (f : Fresh rails k W) (result : PetersenTarget ∈ W) :
    ∃ m ≤ k, ∃ c, Trace (fun a b o => o ∉ base.toFinset ∧ keyedGate physicalKey a b o) base.toFinset m c {PetersenTarget} ∧
      m+1 = 10+c := by
  obtain ⟨S,p,cov,_⟩ := fresh_keyed_prefix physicalKey physicalSign f base.toFinset rails_cover rails_real
  have mem := cov _ result targetHot
  rw [targetKey] at mem
  obtain ⟨I,hi,m,hm,c,tr⟩ := p.no_input_output.schedule {PetersenTarget} (Finset.singleton_subset_iff.mpr mem)
  have eq := demanded (gate := fun a b o => o ∉ base.toFinset ∧ keyedGate physicalKey a b o)
    (fun x y _ _ _ h => keyed_stable physicalKey physicalSign x y h.2) hi tr
  subst I
  exact ⟨m,hm,c,tr,by simpa [ten_inputs] using tr.sink⟩

end Projection


section U2

variable {Ω : Type}
noncomputable local instance : DecidableEq (Func Ω) := Classical.decEq _

def signedKey (atZero : Ω) (f : Func Ω) : Func Ω :=
  if f atZero then flip f else f

theorem signedSign (w : Ω) (f : Func Ω) : negRelated (signedKey w f) f := by
  cases h : f w <;> simp [signedKey,h,negRelated]

theorem signed_flip (w : Ω) (f : Func Ω) : signedKey w (flip f) = signedKey w f := by
  funext x; cases h : f w <;> simp [signedKey,flip,h]

theorem flip_hot {f : Func Ω} (h : nonconstant (flip f)) : nonconstant f := by
  constructor
  · rintro rfl; apply h.2; rfl
  · rintro rfl; apply h.1; rfl

theorem av_coverage (w : Ω) {W : List (Func Ω)} {S : Finset (Func Ω)}
    (cov : ∀ f ∈ W, nonconstant f → signedKey w f ∈ S)
    {v : Func Ω} (h : Av W v) (nc : nonconstant v) : signedKey w v ∈ S := by
  induction h with
  | wire e => exact cov _ e nc
  | zero => exact False.elim (nc.1 rfl)
  | one => exact False.elim (nc.2 rfl)
  | @neg f _ ih =>
    change signedKey w (flip f) ∈ S
    rw [signed_flip]
    exact ih (flip_hot nc)

/-- Compile any signed run. Gates whose output is a constant or already available
up to sign can be discarded. Every remaining gate has two distinct nonconstant
sources and a new normalized output. -/
theorem signed_prefix (w : Ω) {init W : List (Func Ω)} {k} (r : Run init k W)
    (I : Finset (Func Ω)) (hI : ∀ f ∈ init, nonconstant f → signedKey w f ∈ I) :
    ∃ m ≤ k, ∃ S, Prefix (keyedGate (signedKey w)) I m S ∧
      ∀ f ∈ W, nonconstant f → signedKey w f ∈ S := by
  classical
  have add {k W S m} {a b : Func Ω} (j : Bool) (hm : m ≤ k)
      (ha : Av W a) (hb : Av W b) (tr : Prefix (keyedGate (signedKey w)) I m S)
      (cov : ∀ f ∈ W, nonconstant f → signedKey w f ∈ S) :
      ∃ n ≤ k+1, ∃ T, Prefix (keyedGate (signedKey w)) I n T ∧
        ∀ f ∈ bin j a b :: W, nonconstant f → signedKey w f ∈ T := by
    by_cases make : nonconstant (bin j a b) ∧ signedKey w (bin j a b) ∉ S
    · have fresh : ¬ Av W (bin j a b) := fun av => make.2 (av_coverage w cov av make.1)
      obtain ⟨aa,bb,apart,_⟩ := fresh_inputs j ha hb fresh
      have ne : signedKey w a ≠ signedKey w b := fun eq =>
        apart (keys_related _ (signedSign w) eq)
      refine ⟨m+1,by omega, insert (signedKey w (bin j a b)) S,
        Prefix.add tr (av_coverage w cov ha aa) (av_coverage w cov hb bb) ne make.2
          ⟨a,b,j,rfl,rfl,rfl,key_hot _ (signedSign w) make.1⟩,?_⟩
      intro f h nc
      rcases List.mem_cons.mp h with rfl|e
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (cov _ e nc)
    · refine ⟨m,by omega,S,tr,?_⟩
      intro f h nc
      rcases List.mem_cons.mp h with rfl|e
      · by_contra absent; exact make ⟨nc,absent⟩
      · exact cov _ e nc
  induction r with
  | start => exact ⟨0,le_rfl,I,Prefix.start,hI⟩
  | and _ ha hb ih =>
    obtain ⟨m,hm,S,tr,cov⟩ := ih
    exact add false hm ha hb tr cov
  | or _ ha hb ih =>
    obtain ⟨m,hm,S,tr,cov⟩ := ih
    exact add true hm ha hb tr cov

def zeroInput : PInput := fun _ => false

theorem signed_base (f : Func PInput) (h : f ∈ base) (_ : nonconstant f) :
    signedKey zeroInput f ∈ base.toFinset := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem signed_target : signedKey zeroInput PetersenTarget = PetersenTarget := rfl

/-- U2 exclusion needs only search traces from the ten primary registers.
Signs can be chosen afresh on each read, and every wire is normalized at zero. -/
theorem petersen_signed_frontier {W : List (Func PInput)} {k}
    (r : Run base k W) (result : Av W PetersenTarget) :
    ∃ m ≤ k, ∃ c, Trace (fun a b o => o ∉ base.toFinset ∧ keyedGate (signedKey zeroInput) a b o) base.toFinset m c {PetersenTarget} ∧
      m+1 = 10+c := by
  obtain ⟨j,hj,S,p,cov⟩ := signed_prefix zeroInput r base.toFinset signed_base
  have mem := av_coverage zeroInput cov result targetHot
  rw [signed_target] at mem
  obtain ⟨I,hi,m,hm,c,tr⟩ := p.no_input_output.schedule {PetersenTarget} (Finset.singleton_subset_iff.mpr mem)
  have eq := demanded (gate := fun a b o => o ∉ base.toFinset ∧ keyedGate (signedKey zeroInput) a b o)
    (fun x y _ _ _ h => keyed_stable _ (signedSign zeroInput) x y h.2) hi tr
  subst I
  exact ⟨m,by omega,c,tr,by simpa [ten_inputs] using tr.sink⟩

end U2

section Enumeration
variable {Ω : Type}
noncomputable local instance : DecidableEq (Func Ω) := Classical.decEq _

/-- Every preimage of a canonical wire is one of its two Boolean polarities. -/
noncomputable def literalOptions (key : Func Ω → Func Ω) (a : Func Ω) : Finset (Func Ω) :=
  ({a,flip a} : Finset _).filter fun p => key p = a

theorem literalOptions_spec (key : Func Ω → Func Ω) (sgn : ∀ p, negRelated (key p) p)
    (a p : Func Ω) : p ∈ literalOptions key a ↔ key p = a := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · rintro rfl
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    rcases sgn p with e|e
    · simp [e]
    · have ff : flip (flip p) = p := by funext x; simp [flip]
      simp [e,ff]

/-- The two binary gate operations on all physically available input signs. -/
noncomputable def outputOptions (key : Func Ω → Func Ω) (a b : Func Ω) : Finset (Func Ω) :=
  @Finset.filter _ nonconstant (Classical.decPred _) ((literalOptions key a).biUnion fun p => (literalOptions key b).biUnion fun q =>
    {key (bin false p q),key (bin true p q)})

theorem outputOptions_spec (key : Func Ω → Func Ω) (sgn : ∀ p, negRelated (key p) p)
    (a b o : Func Ω) : o ∈ outputOptions key a b ↔ keyedGate key a b o := by
  simp only [outputOptions,Finset.mem_filter,Finset.mem_biUnion,literalOptions_spec key sgn,Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨p,hp,q,hq,h|h⟩,hot⟩
    · exact ⟨p,q,false,hp,hq,h.symm,hot⟩
    · exact ⟨p,q,true,hp,hq,h.symm,hot⟩
  · rintro ⟨p,q,j,hp,hq,rfl,hot⟩
    refine ⟨?_,hot⟩
    refine ⟨p,hp,q,hq,?_⟩
    cases j <;> simp

/-- Enumerate the four retirement masks of the two chosen operands. -/
def keepOptions (L : Finset α) (a b : α) : Finset (Finset α) :=
  ({a,b} : Finset α).powerset.image fun D => L \ D

theorem keepOptions_spec (L K : Finset α) (a b : α) (ha : a ∈ L) (hb : b ∈ L) :
    K ∈ keepOptions L a b ↔ insert a (insert b K) = L := by
  constructor
  · intro hk
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hk
    have sub := Finset.mem_powerset.mp hD
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro (rfl|rfl|h)
      · exact ha
      · exact hb
      · exact h.1
    · intro hx
      by_cases hd : x ∈ D
      · rcases Finset.mem_insert.mp (sub hd) with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl (Finset.mem_singleton.mp e))
      · exact Or.inr (Or.inr ⟨hx,hd⟩)
  · rintro rfl
    apply Finset.mem_image.mpr
    refine ⟨insert a (insert b K) \ K,Finset.mem_powerset.mpr ?_,?_⟩
    · intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hm,hn⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at *
      exact hm.elim Or.inl (fun e => Or.inr (e.resolve_right hn))
    · ext x
      simp only [Finset.mem_sdiff,Finset.mem_insert]
      tauto

/-- Explicit finite successors. Each output includes its charged fan-out credits. -/
def next (outputs : α → α → Finset α) (L : Finset α) : Finset (Finset α × Nat) :=
  L.biUnion fun a => L.biUnion fun b => if a=b then ∅ else
    (outputs a b \ L).biUnion fun o => (keepOptions L a b).image fun K =>
      (insert o K, credit a b K)

theorem next_spec {G : α → α → α → Prop} (outs : α → α → Finset α)
    (spec : ∀ a b o, o ∈ outs a b ↔ G a b o) (L V : Finset α) (cost : Nat) :
    (V,cost) ∈ next outs L ↔ ∃ a b o K,
      a ≠ b ∧ L = insert a (insert b K) ∧ o ∉ L ∧ G a b o ∧ V = insert o K ∧
      cost = credit a b K := by
  constructor
  · intro step
    obtain ⟨a,ha,s⟩ := Finset.mem_biUnion.mp step
    obtain ⟨b,hb,s⟩ := Finset.mem_biUnion.mp s
    split at s
    · simp_all
    · rename_i hab
      obtain ⟨o,ho,s⟩ := Finset.mem_biUnion.mp s
      obtain ⟨K,hK,eq⟩ := Finset.mem_image.mp s
      obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp ho
      exact ⟨a,b,o,K,hab,((keepOptions_spec L K a b ha hb).mp hK).symm,hn,
        (spec a b o).mp hg,(congrArg Prod.fst eq).symm,(congrArg Prod.snd eq).symm⟩
  · rintro ⟨a,b,o,K,hab,rfl,hn,hg,rfl,rfl⟩
    have ha : a ∈ insert a (insert b K) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b K) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    apply Finset.mem_biUnion.mpr
    refine ⟨a,ha,Finset.mem_biUnion.mpr ⟨b,hb,?_⟩⟩
    rw [if_neg hab]
    exact Finset.mem_biUnion.mpr ⟨o,Finset.mem_sdiff.mpr ⟨(spec a b o).mpr hg,hn⟩,
      Finset.mem_image.mpr ⟨K,(keepOptions_spec _ K a b ha hb).mpr rfl,rfl⟩⟩

inductive Walk (outs : α → α → Finset α) (inputs : Finset α) :
    Nat → Nat → Finset α → Prop where
  | start : Walk outs inputs 0 0 inputs
  | step {L V m c spend} : Walk outs inputs m c L → (V,spend) ∈ next outs L →
      Walk outs inputs (m+1) (c+spend) V

theorem walk_iff {G : α → α → α → Prop} (outs : α → α → Finset α)
    (spec : ∀ a b o, o ∈ outs a b ↔ G a b o) {I V m c} :
    Walk outs I m c V ↔ Trace G I m c V := by
  constructor
  · intro t; induction t with
    | start => exact Trace.start
    | step _ hs ih =>
      obtain ⟨a,b,o,K,hab,rfl,fresh,g,rfl,rfl⟩ := (next_spec outs spec _ _ _).mp hs
      exact Trace.step ih hab fresh g
  · intro t; induction t with
    | start => exact Walk.start
    | @step m c K a b o _ hab fresh g ih =>
      exact Walk.step ih ((next_spec outs spec _ _ _).mpr ⟨a,b,o,K,hab,rfl,fresh,g,rfl,rfl⟩)

noncomputable def petersenOptions (key : Func PInput → Func PInput) (a b : Func PInput) :
    Finset (Func PInput) := outputOptions key a b \ base.toFinset

theorem petersenOptions_spec (key : Func PInput → Func PInput) (sgn : ∀ f, negRelated (key f) f)
    (a b o : Func PInput) :
    o ∈ petersenOptions key a b ↔ o ∉ base.toFinset ∧ keyedGate key a b o := by
  rw [petersenOptions,Finset.mem_sdiff,outputOptions_spec key sgn]
  exact and_comm

/-- The original project statement follows from the exclusion of two concrete
finite-successor walks, including their exact gate and fan-out bounds. -/
theorem L_meta_1884_of_frontier_exclusions
    (signed : ∀ c ≤ 8, ¬ Walk (petersenOptions (signedKey zeroInput)) base.toFinset (9+c) c {PetersenTarget})
    (positive : ∀ c ≤ 9, ¬ Walk (petersenOptions physicalKey) base.toFinset (9+c) c {PetersenTarget}) :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x := by
  apply L_meta_1884_of_fresh_exclusions
  · intro k hk W r avail
    obtain ⟨m,hm,c,tr,eq⟩ := petersen_signed_frontier r avail
    have g : m = 9+c := by omega
    subst m
    exact signed c (by omega) ((walk_iff _ (petersenOptions_spec _ (signedSign zeroInput))).mpr tr)
  · intro W f out
    obtain ⟨m,hm,c,tr,eq⟩ := petersen_fresh_frontier f out
    have g : m = 9+c := by omega
    subst m
    exact positive c (by omega) ((walk_iff _ (petersenOptions_spec _ physicalSign)).mpr tr)

end Enumeration


#print axioms L_meta_1884_of_frontier_exclusions
#print axioms petersen_signed_frontier
#print axioms petersen_fresh_frontier
#print axioms fresh_keyed_prefix
#print axioms fresh_schedule

end PetersenFrontier
