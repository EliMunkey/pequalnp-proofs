import PetersenWordCost
import Mathlib.Data.Finset.Card

open PetersenSignedBridge PetersenWordCost

namespace PetersenSignalCut
variable {w : Nat}
abbrev Wire (w : Nat) := BitVec w

def Agree (S : Finset (Wire w)) (i j : Fin w) : Prop := ∀ a ∈ S, PetersenWordCost.read a i = PetersenWordCost.read a j

private theorem basis {W : List (Wire w)} {a : Wire w} (ha : Covered W a) :
    ∃ U : Finset (Wire w), (∀ x ∈ U, x ∈ W) ∧ U.card ≤ 1 ∧
      ∀ i j, Agree U i j → PetersenWordCost.read a i = PetersenWordCost.read a j := by
  rcases ha with h|h
  · rcases List.mem_cons.mp h with rfl|h
    · exact ⟨∅,by simp,by simp,by simp [PetersenWordCost.read]⟩
    · exact ⟨{a},by simpa using h,by simp,fun i j e => e a (by simp)⟩
  · rcases List.mem_cons.mp h with h|h
    · refine ⟨∅,by simp,by simp,?_⟩
      intro i j _
      have h' : a = ~~~0 := by simpa using congrArg (fun v : BitVec w => ~~~v) h
      simp [h',PetersenWordCost.read,i.isLt,j.isLt]
    · refine ⟨{~~~a},by simpa using h,by simp,?_⟩
      intro i j e
      have h' := e (~~~a) (by simp)
      simpa [PetersenWordCost.read,i.isLt,j.isLt] using h'

/-- A demand for q final wire values can be supplied from at most q+k initially
available signals in a k-gate DAG, with no bound on sharing. -/
theorem footprint {I S : List (Wire w)} {k : Nat} (r : Packed I k S)
    (Q : Finset (Wire w)) (hQ : ∀ q ∈ Q, q ∈ S) :
    ∃ U : Finset (Wire w), (∀ a ∈ U, a ∈ I) ∧ U.card ≤ Q.card+k ∧
      ∀ i j, Agree U i j → Agree Q i j := by
  induction r generalizing Q with
  | start => exact ⟨Q,hQ,by omega,fun _ _ h => h⟩
  | @step k W a b r ha hb op ih =>
    let g := gate op a b
    by_cases hg : g ∈ Q
    · obtain ⟨A,hA,cA,dA⟩ := basis ha
      obtain ⟨B,hB,cB,dB⟩ := basis hb
      let T := Q.erase g ∪ A ∪ B
      have hT : ∀ q ∈ T, q ∈ W := by
        intro q h
        rcases Finset.mem_union.mp h with e|e
        · rcases Finset.mem_union.mp e with e|e
          · exact (List.mem_cons.mp (hQ q (Finset.mem_of_mem_erase e))).resolve_left (Finset.ne_of_mem_erase e)
          · exact hA q e
        · exact hB q e
      obtain ⟨U,sub,card,dep⟩ := ih T hT
      refine ⟨U,sub,?_,?_⟩
      · have ab := Finset.card_union_le (Q.erase g) A
        have fin := Finset.card_union_le ((Q.erase g) ∪ A) B
        have e := Finset.card_erase_add_one hg
        change U.card ≤ (Q.erase g ∪ A ∪ B).card + k at card
        omega
      · intro i j ag q hq
        have t := dep i j ag
        by_cases e : q = g
        · subst q
          have aa := dA i j (fun v hv => t v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)))
          have bb := dB i j (fun v hv => t v (Finset.mem_union_right _ hv))
          cases op <;> simp_all [g,gate,PetersenWordCost.read]
        · exact t q (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hq⟩)))
    · have sub : ∀ q ∈ Q, q ∈ W := by
        intro q hq
        exact (List.mem_cons.mp (hQ q hq)).resolve_left (by
          intro e
          apply hg
          change gate op a b ∈ Q
          rw [← e]
          exact hq)
      obtain ⟨U,hU,cU,dep⟩ := ih Q sub
      exact ⟨U,hU,by omega,dep⟩

theorem singleton_footprint {I S : List (Wire w)} {k : Nat} {t : Wire w}
    (r : Packed I k S) (ht : Covered S t) :
    ∃ U : Finset (Wire w), (∀ a ∈ U, a ∈ I) ∧ U.card ≤ k+1 ∧
      ∀ i j, Agree U i j → PetersenWordCost.read t i = PetersenWordCost.read t j := by
  obtain ⟨Q,s,c,d⟩ := basis ht
  obtain ⟨U,s',c',d'⟩ := footprint r Q s
  exact ⟨U,s',by omega,fun i j h => d i j (d' i j h)⟩

/-- Any supplied list of assignments may be used as candidate separation witnesses. -/
abbrev Pairs (w : Nat) := List (Fin w × Fin w)
def forced (W : List (Wire w)) (t x : Wire w) (probes : Pairs w) : Bool :=
  probes.any fun (i,j) =>
    PetersenWordCost.read t i != PetersenWordCost.read t j && (W.all fun y => y == x || PetersenWordCost.read y i == PetersenWordCost.read y j)

theorem must_use {W : List (Wire w)} {t x : Wire w} {probes : Pairs w}
    (h : forced W t x probes = true) {U : Finset (Wire w)} (s : ∀ y ∈ U, y ∈ W)
    (det : ∀ i j, Agree U i j → PetersenWordCost.read t i = PetersenWordCost.read t j) : x ∈ U := by
  obtain ⟨⟨i,j⟩,_,h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true] at h
  by_contra no
  apply h.1
  apply det
  intro y hy
  have test := h.2 y (s y hy)
  simp only [Bool.or_eq_true,beq_iff_eq] at test
  exact test.resolve_left (fun e => no (e ▸ hy))

def forcedSet (W : List (Wire w)) (t : Wire w) (probes : Pairs w) : Finset (Wire w) :=
  (W.filter fun x => forced W t x probes).toFinset

theorem cut {I S : List (Wire w)} {k : Nat} {t : Wire w} (probes : Pairs w)
    (r : Packed I k S) (h : k+1 < (forcedSet I t probes).card) : ¬ Covered S t := by
  intro ht
  obtain ⟨U,s,c,d⟩ := singleton_footprint r ht
  have sub : forcedSet I t probes ⊆ U := by
    intro y hy
    have eq := (List.mem_filter.mp (List.mem_toFinset.mp hy)).2
    exact must_use eq s d
  have le := Finset.card_le_card sub
  omega
end PetersenSignalCut
