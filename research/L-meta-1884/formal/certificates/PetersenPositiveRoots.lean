import PetersenSixteenSuffixes
import PetersenDominantCheck
open PetersenWordCost PetersenPackedPin PetersenDominantCheck PetersenElevenAntichain PetersenPhysicalWords
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenPositiveRoots
set_option maxHeartbeats 0
set_option maxRecDepth 160000
set_option exponentiation.threshold 2048
abbrev Debt := PetersenElevenCensus.Debt
def remaining : List (BitVec 38 × Bool) := [(0x5c3f4cbc,false),(0x5c3f4cbc,true),(0x685bccec,false),(0x685bccec,true),(0x74648cf0,false),(0x74648cf0,true),(0x1c99f4f2c,false),(0x1c99f4f2c,true),(0x251f362af9,false),(0x254b1b667d,false),(0x30683b7e2e,false),(0x30683b7e2e,true),(0x31a1a73f0e,false),(0x31a1a73f0e,true)]
private def killed : List (BitVec 38 × Bool) := [(0x2,true),(0xc,true)]
private def proj0 (i : Fin 512) : Fin 38 := (#[21,21,30,2,7,11,5,2,17,9,27,3,4,4,4,4,10,11,16,2,11,11,5,5,9,9,17,3,4,4,4,4,18,12,14,12,18,12,5,12,17,13,17,3,4,13,4,13,18,12,16,2,18,12,5,12,17,13,17,13,4,4,4,4,21,21,19,19,21,21,19,2,37,37,20,3,4,4,20,3,23,23,19,19,23,23,23,19,24,24,24,3,24,24,4,24,26,12,19,19,26,12,5,19,25,13,20,3,4,4,4,3,23,23,23,19,23,12,5,12,24,13,20,20,4,4,24,24,36,36,30,2,28,28,28,5,27,37,27,3,4,4,4,3,31,31,31,2,28,28,31,2,32,32,32,3,32,32,32,4,33,33,33,12,33,33,33,12,34,34,34,3,34,4,34,3,31,31,33,2,28,33,5,33,32,13,32,3,32,13,4,3,35,36,19,19,28,28,5,19,37,37,20,3,4,4,4,20,31,23,31,19,31,28,23,19,24,24,20,3,32,24,4,24,33,12,19,33,33,28,5,28,34,34,20,13,4,34,34,3,33,33,19,33,33,31,33,5,34,32,24,3,32,13,24,13,7,11,10,2,7,11,5,5,6,6,6,6,6,6,4,6,11,11,10,2,11,11,5,2,6,6,6,3,6,4,6,4,15,12,15,12,15,12,15,2,6,6,6,6,4,13,4,4,15,15,15,12,15,15,5,2,6,13,6,3,6,13,6,6,22,22,22,19,22,22,22,2,6,6,6,6,6,4,20,3,23,23,19,2,23,23,23,19,6,24,24,24,24,6,24,4,15,15,15,15,22,12,15,15,6,13,6,13,4,6,4,13,23,23,15,2,23,15,15,22,24,6,6,20,6,13,20,3,30,29,30,2,28,28,5,28,6,6,6,6,4,4,4,4,31,31,31,31,28,28,28,5,6,6,32,3,32,4,32,4,15,15,15,12,28,15,28,28,34,13,6,6,4,13,6,3,33,12,15,33,15,33,15,2,6,13,34,32,34,32,34,3,22,22,22,22,22,28,28,22,6,6,6,3,6,6,6,20,23,23,31,23,23,31,5,31,32,24,24,20,4,4,32,3,33,12,15,33,28,28,22,28,6,34,6,6,4,6,34,3,23,15,31,19,31,22,23,22,6,34,34,32,6,32,4,13] : Array (Fin 38))[i.val]?.getD 0
private theorem same0 : PetersenPackedPin.project proj0 target = PetersenNineLift.nine := by decide +kernel
private def proj1 (i : Fin 512) : Fin 38 := (#[21,26,27,0,7,7,4,4,16,14,17,0,5,5,4,4,14,26,25,0,18,26,4,4,16,14,17,0,5,5,4,0,16,8,9,0,11,8,4,4,10,8,17,0,5,8,4,4,18,8,17,0,18,8,4,4,16,8,17,0,5,8,4,0,7,30,6,0,7,7,6,6,30,30,6,0,5,5,6,0,15,15,6,0,15,15,6,4,15,15,6,0,15,5,6,4,10,8,6,6,11,8,4,0,10,8,6,0,5,5,4,6,15,15,6,6,15,15,4,6,15,15,6,6,5,5,4,4,36,35,37,0,28,28,4,4,30,30,27,0,28,28,4,0,33,33,34,0,28,28,34,0,33,33,34,34,33,28,34,4,31,31,32,0,31,31,4,0,31,8,32,0,31,5,32,32,33,8,32,34,33,33,4,4,31,33,34,34,5,5,32,4,30,30,6,0,28,28,4,6,30,30,6,0,28,5,4,6,33,33,34,34,33,28,6,4,15,33,6,34,5,5,34,0,31,31,6,6,28,31,6,4,31,8,6,6,5,8,32,0,31,8,34,0,15,33,32,4,33,15,34,32,15,5,32,4,35,35,25,0,21,26,4,0,19,19,20,20,5,5,4,4,26,26,25,0,26,26,4,4,19,19,20,20,19,5,20,0,23,8,24,24,23,8,24,0,19,23,24,0,5,23,4,4,23,8,24,24,23,23,4,24,19,8,24,24,19,19,4,4,22,22,6,0,22,22,6,4,22,19,6,0,5,22,6,20,15,22,6,6,15,15,6,4,22,19,20,6,19,15,20,20,23,8,6,24,22,22,6,24,19,23,6,20,19,22,4,20,23,23,6,0,15,15,24,4,19,22,20,20,19,5,4,24,35,35,37,0,28,28,4,4,19,19,20,20,28,5,4,4,33,33,34,34,33,33,4,0,19,19,34,34,5,19,34,20,31,23,24,0,23,23,24,24,23,23,32,0,31,5,24,0,23,33,34,0,23,33,4,0,33,31,34,32,28,5,4,0,22,22,6,6,22,22,4,4,22,19,20,20,19,28,20,20,33,22,34,6,33,33,6,34,15,22,34,0,33,5,20,0,23,8,24,24,28,23,32,4,22,19,32,32,23,23,20,4,15,15,24,24,23,31,34,6,31,31,20,32,5,19,24,4] : Array (Fin 38))[i.val]?.getD 0
private theorem same1 : PetersenPackedPin.project proj1 target = PetersenNineLift.nine := by decide +kernel
private theorem dead0 (nine : PetersenNineLift.Hard 15) : Debt (0x2,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  exact PetersenDominantCheck.check_sound proj0 (inputs 9) 15 target [] (state (0x2,true)) 17 (same0 ▸ nine) (by decide +kernel) hm plain
private theorem dead1 (nine : PetersenNineLift.Hard 15) : Debt (0xc,true) := by
  intro m hm credit tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  exact PetersenDominantCheck.check_sound proj1 (inputs 9) 15 target [] (state (0xc,true)) 17 (same1 ▸ nine) (by decide +kernel) hm plain
private theorem cover : PetersenElevenCensus.remaining.all (fun c => remaining.contains c || killed.contains c) = true := by decide
theorem original (nine : PetersenNineLift.Hard 15) (left : ∀ v∈remaining, Debt v) :
    ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool), FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x := by
  apply PetersenSixteenSuffixes.original nine; intro c hc
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp cover c hc) with live|dead
  · exact left c (List.contains_iff_mem.mp live)
  · have v := List.contains_iff_mem.mp dead; unfold killed at v
    simp only [List.mem_cons,List.not_mem_nil,or_false] at v
    rcases v with rfl|rfl
    · exact dead0 nine
    · exact dead1 nine
theorem remaining_size : remaining.length = 14 := by decide
#print axioms original
end PetersenPositiveRoots
