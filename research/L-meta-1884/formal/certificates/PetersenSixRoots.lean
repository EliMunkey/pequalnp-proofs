import PetersenPositiveRoots
import PetersenPositiveCheck
open PetersenPhysicalWords PetersenElevenAntichain PetersenWordCost PetersenPositiveRoots
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenSixRoots
set_option maxRecDepth 120000
set_option maxHeartbeats 0
/-- Each representative is the OR of two positive input wires. Both signs of the marked input are supplied. -/
def outputs : List (BitVec 38) := [0x5c3f4cbc,0x685bccec,0x74648cf0,0x1c99f4f2c,0x30683b7e2e,0x31a1a73f0e]
def basis (w : BitVec 38) : List (BitVec 38) := 0 :: (~~~0) :: w :: PetersenEleven.sources
def Suffix (w : BitVec 38) : Prop := PetersenPhysicalProjection.NoPhysical (basis w) target 17
theorem count : outputs.length=6 := by decide
private def row0 : Fin 38 → Fin 38 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
private theorem same0 : PetersenPackedPin.project row0 target=target := by decide +kernel
private def row1 : Fin 38 → Fin 38 := ![2,12,15,15,19,22,5,21,1,14,7,26,33,33,29,28,30,30,35,6,6,25,4,0,0,27,37,10,23,18,11,8,8,31,31,9,17,17]
private theorem same1 : PetersenPackedPin.project row1 target=target := by decide +kernel
private def row2 : Fin 38 → Fin 38 := ![0,4,5,5,1,2,8,9,6,7,10,11,28,28,27,31,30,30,29,19,19,21,23,22,22,35,37,14,12,18,17,15,15,33,33,25,26,26]
private theorem same2 : PetersenPackedPin.project row2 target=target := by decide +kernel
private def row3 : Fin 38 → Fin 38 := ![2,1,0,0,5,4,19,21,12,14,25,26,8,8,9,23,17,17,18,6,6,7,22,15,15,10,11,27,28,35,37,33,33,31,31,29,30,30]
private theorem same3 : PetersenPackedPin.project row3 target=target := by decide +kernel
private def row4 : Fin 38 → Fin 38 := ![23,8,0,0,22,6,19,10,31,35,27,30,1,1,9,2,37,37,29,4,4,7,5,28,28,21,11,25,15,14,17,33,33,12,12,18,26,26]
private theorem same4 : PetersenPackedPin.project row4 target=target := by decide +kernel
private def row5 : Fin 38 → Fin 38 := ![28,5,2,2,33,12,31,18,4,27,9,17,19,19,21,23,37,37,25,1,1,14,8,0,0,35,26,29,15,10,11,6,6,22,22,7,30,30]
private theorem same5 : PetersenPackedPin.project row5 target=target := by decide +kernel
private theorem transport0 (h : Suffix 0x5c3f4cbc) : Debt (0x5c3f4cbc,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x5c3f4cbc) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x5c3f4cbc,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport1 (h : Suffix 0x5c3f4cbc) : Debt (0x5c3f4cbc,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x5c3f4cbc) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x5c3f4cbc,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport2 (h : Suffix 0x685bccec) : Debt (0x685bccec,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x685bccec,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport3 (h : Suffix 0x685bccec) : Debt (0x685bccec,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x685bccec,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport4 (h : Suffix 0x685bccec) : Debt (0x74648cf0,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row1 target) 17 := same1 ▸ h
  exact PetersenPositiveCheck.sound row1 small (by decide) (p := []) (L := state (0x74648cf0,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport5 (h : Suffix 0x74648cf0) : Debt (0x74648cf0,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x74648cf0) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x74648cf0,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport6 (h : Suffix 0x685bccec) : Debt (0x1c99f4f2c,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row2 target) 17 := same2 ▸ h
  exact PetersenPositiveCheck.sound row2 small (by decide) (p := []) (L := state (0x1c99f4f2c,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport7 (h : Suffix 0x1c99f4f2c) : Debt (0x1c99f4f2c,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x1c99f4f2c) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x1c99f4f2c,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport8 (h : Suffix 0x5c3f4cbc) : Debt (0x251f362af9,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x5c3f4cbc) (PetersenPackedPin.project row3 target) 17 := same3 ▸ h
  exact PetersenPositiveCheck.sound row3 small (by decide) (p := []) (L := state (0x251f362af9,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport9 (h : Suffix 0x685bccec) : Debt (0x254b1b667d,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row4 target) 17 := same4 ▸ h
  exact PetersenPositiveCheck.sound row4 small (by decide) (p := []) (L := state (0x254b1b667d,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport10 (h : Suffix 0x5c3f4cbc) : Debt (0x30683b7e2e,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x5c3f4cbc) (PetersenPackedPin.project row2 target) 17 := same2 ▸ h
  exact PetersenPositiveCheck.sound row2 small (by decide) (p := []) (L := state (0x30683b7e2e,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport11 (h : Suffix 0x30683b7e2e) : Debt (0x30683b7e2e,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x30683b7e2e) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x30683b7e2e,true)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport12 (h : Suffix 0x685bccec) : Debt (0x31a1a73f0e,false) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x685bccec) (PetersenPackedPin.project row5 target) 17 := same5 ▸ h
  exact PetersenPositiveCheck.sound row5 small (by decide) (p := []) (L := state (0x31a1a73f0e,false)) (fuel := 17) (by decide +kernel) hm plain
private theorem transport13 (h : Suffix 0x31a1a73f0e) : Debt (0x31a1a73f0e,true) := by
  intro m hm c tail
  have plain := PetersenNinePositive.tailGate (fun _ _ _ g => g.1) tail.toTail
  have small : PetersenPhysicalProjection.NoPhysical (basis 0x31a1a73f0e) (PetersenPackedPin.project row0 target) 17 := same0 ▸ h
  exact PetersenPositiveCheck.sound row0 small (by decide) (p := []) (L := state (0x31a1a73f0e,true)) (fuel := 17) (by decide +kernel) hm plain
theorem original (nine : PetersenNineLift.Hard 15) (h : ∀ w ∈ outputs, Suffix w) :
    ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool), FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x := by
  apply PetersenPositiveRoots.original nine
  intro v hv; unfold PetersenPositiveRoots.remaining at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact transport0 (h _ (by decide))
  · exact transport1 (h _ (by decide))
  · exact transport2 (h _ (by decide))
  · exact transport3 (h _ (by decide))
  · exact transport4 (h _ (by decide))
  · exact transport5 (h _ (by decide))
  · exact transport6 (h _ (by decide))
  · exact transport7 (h _ (by decide))
  · exact transport8 (h _ (by decide))
  · exact transport9 (h _ (by decide))
  · exact transport10 (h _ (by decide))
  · exact transport11 (h _ (by decide))
  · exact transport12 (h _ (by decide))
  · exact transport13 (h _ (by decide))
#print axioms original
end PetersenSixRoots
