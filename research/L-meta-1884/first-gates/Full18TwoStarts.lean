import PetersenProjectedRule
import Full18Early1
import Full18Early2
import PetersenRootBound
open PetersenWordCost PetersenPackedPin PetersenProjectedRule PetersenLayerCheck
namespace Full18
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
theorem only_two (edge : Blocked Root17.tgt 16 live6) (nonedge : Blocked Root17.tgt 16 live7) : Blocked Root17.tgt 17 Root17.primary := by
  rw [←Root17.tgt_eq,←Root17.raw_eq]; apply PetersenRootOrbit.two_pairs 17
  · rw [Root17.tgt_eq,Root17.raw_eq]; exact earlyFirst1 edge
  · rw [Root17.tgt_eq,Root17.raw_eq]; exact earlyFirst2 nonedge
#print axioms only_two
end Full18
