import PetersenWordEnum

open PetersenWordCost
namespace PetersenGraphCosts

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 16000 in
theorem mask7_lower : NoAtMost (inputs 3) (graphTarget 3 [(0, 1), (1, 2)]) 1 := by
  apply lower_of_reject
  change Reject (0xc8 : BitVec 8) 1 [0xaa, 0xcc, 0xf0]
  apply rejectBool_sound
  decide

#print axioms mask7_lower
end PetersenGraphCosts
