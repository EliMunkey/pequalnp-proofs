import PetersenWordEnum

open PetersenWordCost
namespace PetersenGraphCosts

set_option maxHeartbeats 15000000 in
set_option maxRecDepth 16000 in
theorem mask3_lower : NoAtMost (inputs 2) (graphTarget 2 [(0, 1)]) 0 := by
  apply lower_of_reject
  change Reject (0x8 : BitVec 4) 0 [0xa, 0xc]
  apply rejectBool_sound
  decide

#print axioms mask3_lower
end PetersenGraphCosts
