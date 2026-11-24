import BSFirst1
import BSFirst2
import RSRange

open PetersenWordCost PetersenLayerCheck PetersenVerifiedGroup PetersenFrontierSymmetry
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Root17
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem closed (adj : Adj) : Blocked tgt 16 primary := by
  rw [←tgt_eq,←raw_eq]
  apply PetersenRootOrbit.two_pairs 16
  · rw [tgt_eq,raw_eq]
    exact pair1 adj
  · rw [tgt_eq,raw_eq]
    exact pair2 adj

theorem public_lower (adj : Adj) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 17 ≤ C.size :=
  public_of_closure (closed adj) C σ u fan computes
#print axioms public_lower
end Root17
