import PetersenForwardSearch
open PetersenWordCost PetersenSignalCut
namespace PetersenForwardSearch

private theorem from_signs {w} {W : List (BitVec w)} {a} (h : a ∈ signs W) : Covered W a := by
  rcases List.mem_append.mp h with h|h
  · exact Or.inl h
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    exact Or.inr (by simpa using hb)

private theorem step_witness {w} {W : List (BitVec w)} {v} (h : v ∈ steps W) :
    ∃ a b, Covered W a ∧ Covered W b ∧ v = gate false a b := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp h)
  obtain ⟨ha,hb⟩ := List.mem_product.mp hab
  exact ⟨a,b,from_signs ha,from_signs hb,rfl⟩

theorem search_complete {w} {t : BitVec w} (probes : Pairs w) (cache : List (Entry t)) :
    ∀ k W, Reject t k W → search t probes cache k W = true := by
  intro k
  induction k with
  | zero =>
    intro W h
    change (!cb W t) = true
    cases hit : cb W t with
    | false => rfl
    | true => exact (h (cb_spec.mp hit)).elim
  | succ k ih =>
    intro W h
    simp only [search]
    split
    next => rfl
    split
    next ht => exact (reject_covered h (cb_spec.mp ht)).elim
    split
    next => rfl
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ih _ (reject_lower (by omega) h),List.all_eq_true.mpr ?_⟩
    intro v hv
    obtain ⟨a,b,ha,hb,rfl⟩ := step_witness hv
    exact Bool.or_eq_true_iff.mpr (Or.inr (ih _ (h a b ha hb false)))

theorem search_iff {w} {t : BitVec w} (probes : Pairs w) (cache : List (Entry t))
    (k : Nat) (W : List (BitVec w)) :
    search t probes cache k W = true ↔ Reject t k W :=
  ⟨search_sound probes cache k W,search_complete probes cache k W⟩

#print axioms search_iff
end PetersenForwardSearch
