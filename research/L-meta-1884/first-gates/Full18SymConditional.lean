import PetersenProjectedRule
import Full18TwoStarts
import Full18Quot6
import Full18Quot7
open PetersenWordCost PetersenPackedPin PetersenProjectedRule PetersenLayerCheck
namespace Full18
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
theorem symmetry_closure (h : Needs) : Blocked Root17.tgt 17 Root17.primary := only_two (quotient6 h) (quotient7 h)
theorem signed (h : Needs) : NoAtMost (inputs 10) Root17.tgt 17 :=
  PetersenRootBound.signed_of_closure (symmetry_closure h)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PetersenSignedBridge
theorem symmetry_public (h : Needs) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 18 ≤ C.size :=
  PetersenRootBound.public_of_closure (symmetry_closure h) C σ u fan computes
#print axioms signed
#print axioms symmetry_public
end Full18
