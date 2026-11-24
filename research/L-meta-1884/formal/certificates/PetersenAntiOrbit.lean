import PetersenAntiStep
import PetersenAntiSymmetry
open PetersenMonotoneFrontier PetersenAntichain PetersenFrontierSymmetry PetersenWordCost PetersenFrontier
namespace PetersenAntiOrbit
variable {w : Nat}
local notation "W" => BitVec w

theorem blocked (p : Fin w ≃ Fin w) {I L R : List W} {t : W} {d : Nat}
    (stable : act p t=t) (src : I.toFinset.map (rowEmb p)=I.toFinset)
    (matching : L.toFinset.map (rowEmb p)=R.toFinset) (ok : PetersenAntiStep.Blocked I t d R) :
    PetersenAntiStep.Blocked I t d L := by
  intro m hm c tail
  have moved := PetersenAntiSymmetry.map p tail
  have e : rowEmb p t=t := stable
  rw [src,matching,Finset.map_singleton,e,stable] at moved
  exact ok m hm c moved

#print axioms blocked
end PetersenAntiOrbit
