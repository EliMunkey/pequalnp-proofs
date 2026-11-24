import PetersenNineBoundary
import PetersenElevenCensus
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenSixteenSuffixes

/-- A signed lower bound on deleting one vertex and sixteen ordinary positive suffixes suffice. -/
theorem original
    (nine : PetersenNineLift.Hard 15)
    (cases : ∀ v ∈ PetersenElevenCensus.remaining, PetersenElevenCensus.Debt v) :
    ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool),
      FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x :=
  L_meta_1884_of_exclusions (PetersenPackedRoot.signed_of_words (PetersenNineLift.signed nine))
    (PetersenElevenCensus.close_small (PetersenNineBoundary.positive nine) cases)

#print axioms original
end PetersenSixteenSuffixes
