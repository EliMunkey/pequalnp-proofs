import PetersenForwardSearch

open PetersenSignedBridge PetersenWordCost PetersenSignalCut PetersenForwardSearch

namespace PetersenPathFour

/-- Vertices 0,1,2,3 induce the path 0-1-2-3 in the original Petersen graph. -/
def input : List (BitVec 16) := [0xAAAA,0xCCCC,0xF0F0,0xFF00]
def target : BitVec 16 := 0xF8C8
def probes : Pairs 16 := [(1,3),(2,3),(2,6),(4,6),(4,12),(5,7),(5,13),(8,12),
  (9,11),(9,13),(10,11),(10,14)]

theorem table_agrees : ∀ v : Fin 16, PetersenWordCost.read target v =
    ((v.val.testBit 0 && v.val.testBit 1) || (v.val.testBit 1 && v.val.testBit 2) ||
      (v.val.testBit 2 && v.val.testBit 3)) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exhaustive : search target probes [] 3 input = true := by decide

theorem no_three_gates : NoAtMost input target 3 :=
  lower_of_reject (search_sound probes [] 3 input exhaustive)

#print axioms no_three_gates
end PetersenPathFour
