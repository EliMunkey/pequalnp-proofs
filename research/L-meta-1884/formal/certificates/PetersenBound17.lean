import BSPublic
import Q1020K12Closing
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenBound17

theorem public_lower (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 17 ≤ C.size :=
  Root17.public_lower (Orbits1020Cost12.bound ThetaCert.bound) C σ u fan computes

#print axioms public_lower
end PetersenBound17
