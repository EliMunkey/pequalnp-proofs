import Full18EighteenStarts
import PetersenScalarClosure
import PetersenShared22
open PetersenWordCost PetersenPackedPin PetersenPhysicalWords PetersenPhysicalProjection
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenThreeChecks
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def rows : Fin 30 → Fin 38 := ![0,1,2,4,5,6,7,8,9,10,11,12,14,15,17,18,19,21,22,23,25,26,27,28,29,30,31,33,35,37]
def inputs30 := PetersenScalarSource.pure.map (PetersenPackedPin.project rows)
def target30 := PetersenPackedPin.project rows PetersenPhysicalWords.target
def Pure := NoPhysical inputs30 target30 18
theorem pure_of_small (h : Pure) : NoPhysical PetersenScalarSource.pure PetersenPhysicalWords.target 18 := by
  intro n le W run mem
  apply h n le _ (PetersenShared22.mapRun rows run)
  change PetersenPackedPin.project rows PetersenPhysicalWords.target ∈ W.map (PetersenPackedPin.project rows)
  exact List.mem_map_of_mem mem

theorem original
    (full : NoAtMost (inputs 10) Root17.tgt 17)
    (pure : Pure) (shared : PetersenShared22.Hard 15)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (small : C.size ≤ 18) :
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x := by
  have raw := full
  rw [← Root17.origin_eq] at raw
  have all := (PetersenShared22.equivalent 15).mp shared
  have ordinary := all false false
  have e : PetersenCubicScalar.scalar false false=PetersenNineData.label := by decide +kernel
  rw [e] at ordinary
  exact PetersenScalarClosure.original (PetersenPackedRoot.signed_of_words raw) (pure_of_small pure)
    ordinary (all true false) (all true true) C σ u fan small

theorem using_starts
    (h : Full18.RemainingStarts) (pure : Pure) (shared : PetersenShared22.Hard 15)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (small : C.size ≤ 18) :
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x :=
  original (Full18.signed (Full18.from_remaining_starts h)) pure shared C σ u fan small
#print axioms original
#print axioms using_starts
end PetersenThreeChecks
