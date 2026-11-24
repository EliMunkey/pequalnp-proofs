import PetersenPermuteWord

open PetersenWordCost PetersenSymmetry PetersenPermuteWord
namespace PetersenPermuteGroup
variable {w : Nat}

/-- A right inverse suffices; this covers every element of a graph symmetry group
even when the permutation has order greater than two. -/
def actionOfRightInverse (hw : 0<w) (r inv : Fin w → Fin w) (right : ∀ i, r (inv i) = i)
    (zero : r ⟨0,hw⟩ = ⟨0,hw⟩) (p : List (Nat × BitVec w))
    (verify : ∀ i : Fin w, picked p i = [(r i).val]) : Action w :=
  ofRows hw r (fun i => ⟨inv i,right i⟩) zero (pieces p) (by
    intro a i; rw [pieces_read,verify]; simp [PetersenWordCost.read])

#print axioms actionOfRightInverse
end PetersenPermuteGroup
