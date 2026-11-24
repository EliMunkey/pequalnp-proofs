import PetersenPhysicalCut

open PetersenFrontier PetersenFrontierSearch PetersenPhysicalWords PetersenPhysicalCut
namespace PetersenPhysicalSearch
variable {w : Nat}
abbrev B := BitVec w
abbrev Allowed (I : Finset (BitVec w)) (p a b o : BitVec w) := o ∉ I ∧ WordGate p a b o

def moves (I : List (BitVec w)) (p : BitVec w) (L : List (BitVec w)) (spare : Nat) :
    List (List (BitVec w)) :=
  L.flatMap fun a => L.flatMap fun b => if a.toNat ≥ b.toNat then [] else
    (choices p a b).eraseDups.flatMap fun o => if L.contains o || I.contains o then [] else
      [false,true].flatMap fun ka => [false,true].filterMap fun kb =>
        if ka.toNat+kb.toNat ≤ spare then some (o :: kept L a b ka kb) else none

private theorem gate_swap (p : BitVec w) {a b o : BitVec w} (h : WordGate p a b o) : WordGate p b a o := by
  obtain ⟨⟨x,y⟩,pq,hs⟩ := List.mem_flatMap.mp h
  obtain ⟨hx,hy⟩ := List.mem_product.mp pq
  apply List.mem_flatMap.mpr
  refine ⟨(y,x),List.mem_product.mpr ⟨hy,hx⟩,?_⟩
  simpa only [BitVec.and_comm y x,BitVec.or_comm y x] using hs

private theorem move_ordered {I L : List (BitVec w)} {p a b o : BitVec w} {K : Finset (BitVec w)}
    (old : L.toFinset = insert a (insert b K)) (lt : a.toNat < b.toNat) (fresh : o ∉ L.toFinset)
    (g : Allowed I.toFinset p a b o) {spare : Nat} (h : credit a b K ≤ spare) :
    ∃ V ∈ moves I p L spare, V.toFinset = insert o K := by
  let ka := decide (a ∈ K)
  let kb := decide (b ∈ K)
  have cost : ka.toNat + kb.toNat = credit a b K := by
    by_cases ha : a∈K <;> by_cases hb : b∈K <;> simp [credit,ha,hb,ka,kb]
  have am : a∈L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_self ..)
  have bm : b∈L := List.mem_toFinset.mp (old ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  refine ⟨o :: kept L a b ka kb,?_,by simp only [List.toFinset_cons]; rw [kept_eq old]⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,am,List.mem_flatMap.mpr ⟨b,bm,?_⟩⟩
  simp only [ite_eq_right (Nat.not_le.mpr lt),List.mem_flatMap]
  refine ⟨o,List.mem_eraseDups.mpr g.2,?_⟩
  have miss : (L.contains o || I.contains o) = false := by
    have ml := fun (e : o∈L) => fresh (List.mem_toFinset.mpr e)
    have mi := fun (e : o∈I) => g.1 (List.mem_toFinset.mpr e)
    simpa using (And.intro ml mi)
  simp only [miss,Bool.false_eq_true,ite_false,List.mem_flatMap]
  have bit (v : Bool) : v∈[false,true] := by cases v <;> simp
  exact ⟨ka,bit ka,List.mem_filterMap.mpr ⟨kb,bit kb,by simp [cost,h]⟩⟩

private theorem move_all {I L : List (BitVec w)} {p a b o : BitVec w} {K : Finset (BitVec w)}
    (old : L.toFinset = insert a (insert b K)) (ne : a ≠ b) (fresh : o ∉ L.toFinset)
    (g : Allowed I.toFinset p a b o) {spare : Nat} (h : credit a b K ≤ spare) :
    ∃ V ∈ moves I p L spare, V.toFinset = insert o K := by
  by_cases lt : a.toNat < b.toNat
  · exact move_ordered old lt fresh g h
  · have neq : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
    have rev : b.toNat < a.toNat := by omega
    apply move_ordered (a := b) (b := a) (by simpa only [Finset.insert_comm] using old) rev fresh
       ⟨g.1,gate_swap p g.2⟩
    simpa [credit,Nat.add_comm] using h

def Blocked (I : List (BitVec w)) (p t : BitVec w) (fuel : Nat) (L : List (BitVec w)) : Prop :=
  ∀ m ≤ fuel, ∀ c, ¬ Tail (Allowed I.toFinset p) L.toFinset m c {t}

def sameState (a b : List (BitVec w)) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

private theorem sameState_eq {a b : List (BitVec w)} (h : sameState a b = true) : a.toFinset = b.toFinset := by
  obtain ⟨ab,ba⟩ := Bool.and_eq_true_iff.mp h
  ext x
  simpa only [List.mem_toFinset] using
    (show x∈a ↔ x∈b from ⟨fun e => List.contains_iff_mem.mp (List.all_eq_true.mp ab x e),
      fun e => List.contains_iff_mem.mp (List.all_eq_true.mp ba x e)⟩)

def node (I : List (BitVec w)) (p t : BitVec w) (negative : List (Fin w))
    (reject : Nat → List (BitVec w) → Bool) (fuel : Nat) (children : List (List (BitVec w)))
    (L : List (BitVec w)) : Bool :=
  reject fuel L || (!L.contains t && (moves I p L (fuel+1-L.toFinset.card)).all fun V =>
    !fits p t negative V || reject (fuel-1) V || children.any (sameState V))

private theorem tail_count {I L T : Finset (BitVec w)} {p : BitVec w} {m c : Nat} (tail : Tail (Allowed I p) L m c T) : T.card + m = L.card + c := by
  induction tail with
  | nil => simp
  | @step K a b o m c T ne fresh g _ ih =>
    have one := Trace.account (Trace.step (gate := Allowed I p) (Trace.start (inputs := insert a (insert b K))) ne fresh g)
    simp only [Nat.zero_add] at one
    omega

theorem node_sound {I : List (BitVec w)} {p t : BitVec w} (present : p ∈ I.toFinset)
    (neg : List (Fin w)) (reject : Nat → List (BitVec w) → Bool)
    (ok : ∀ f L, reject f L = true → Blocked I p t f L) {d children L}
    (here : node I p t neg reject (d+1) children L = true)
    (checked : ∀ V∈children, Blocked I p t d V) : Blocked I p t (d+1) L := by
  rcases Bool.or_eq_true_iff.mp here with closed|go
  · exact ok _ _ closed
  intro m hm c tail
  obtain ⟨miss,all⟩ := Bool.and_eq_true_iff.mp go
  have count := tail_count tail
  simp only [Finset.card_singleton] at count
  generalize eq : L.toFinset = S at tail
  generalize endEq : ({t} : Finset _) = T at tail
  cases tail with
  | nil =>
    have mem : t ∈ L.toFinset := (eq.trans endEq.symm) ▸ Finset.mem_singleton_self _
    simpa [List.mem_toFinset.mp mem] using miss
  | @step K a b o m c T ne fresh g tail =>
    obtain ⟨V,hv,hV⟩ := move_all eq ne (eq ▸ fresh) g (by omega : credit a b K ≤ d+1+1-L.toFinset.card)
    have eval := List.all_eq_true.mp all _ hv
    have r : Tail (Allowed I.toFinset p) V.toFinset m c {t} := hV ▸ endEq.symm ▸ tail
    have yes := fits_tail present V r neg
    change ((!fits p t neg V || reject d V) || children.any (sameState V)) = true at eval
    simp only [yes,Bool.not_true,Bool.false_or,Bool.or_eq_true_iff,List.any_eq_true] at eval
    rcases eval with h|⟨v,mem,same⟩
    · exact ok d V h _ (by omega) _ r
    · exact checked v mem _ (by omega) _ (sameState_eq same ▸ r)

end PetersenPhysicalSearch
