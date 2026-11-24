import PetersenLayerCheck
import PetersenFastNode
open PetersenSignedBridge PetersenWordCost PetersenLayerCheck PetersenFrontierSearch PetersenPackedFrontier
namespace PetersenSignedDemand
variable {w : Nat}

/-- Concrete pivotal row pairs can force every primary to be present even after slicing. -/
def force (t : BitVec w) (I : List (BitVec w)) (rows : List (Nat × Nat)) (a : BitVec w) : Bool :=
  rows.any fun (i,j) => PetersenFastNode.mismatch t (I.filter (· != a)) i j

theorem lower {I : List (BitVec w)} {t : BitVec w} {K : Nat}
    (hw : 0<w) (hn : ∀ a∈I, a.getLsbD 0 = false) (ht : t.getLsbD 0 = false)
    (hot : PetersenFrontier.nonconstant (PetersenWordCost.read t))
    (rows : List (Nat × Nat)) (needs : I.all (force t I rows) = true) (closed : Blocked t K I) :
    NoAtMost I t K := by
  intro k hk W r o
  obtain ⟨U,sub,m,hm,c,tr,_⟩ := realize hw I t hn ht hot r o
  have tail := to_tail tr
  have full : U=I.toFinset := by
    apply Finset.Subset.antisymm sub
    intro a ha
    by_contra missing
    obtain ⟨⟨i,j⟩,_,hit⟩ := List.any_eq_true.mp (List.all_eq_true.mp needs a (List.mem_toFinset.mp ha))
    simp only [PetersenFastNode.mismatch,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne,List.all_eq_true,beq_iff_eq] at hit
    obtain ⟨⟨⟨hi,hj⟩,bad⟩,same⟩ := hit
    apply bad
    apply tail_agree tail ⟨i,hi⟩ ⟨j,hj⟩ _ t (Finset.mem_singleton_self _)
    intro x hx
    have ne : x ≠ a := fun eq => missing (eq ▸ hx)
    exact same x (List.mem_filter.mpr ⟨List.mem_toFinset.mp (sub hx),by simp [ne]⟩)
  exact closed m (by omega) c (full ▸ tail)

end PetersenSignedDemand
