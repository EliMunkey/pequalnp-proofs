import RSIndex
import RSRules
import PetersenPairHints
import BSNode7
open PetersenWordCost PetersenLayerCheck PetersenBank PetersenPackedPin
namespace Root17
set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
def nextf2 : Array Nat := #[5,7,0,3]
def hintsf2 : List Nat := [2055,2055,2058,0,9232,20505,9233,1,2058,20505,2058,2,2055,2055,9233,3]
theorem pair2 (adj : Adj) : PetersenRootOrbit.DeadPair tgt 16 primary.toFinset (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : W) := by
  apply PetersenPairHints.killed (nxt := nextf2.map live) (hs := hintsf2)
  · decide +kernel
  · apply PetersenRuleBank.children (tab := rules) (which := whichRule) (ids := ids) (more := [7]) (ok := validRules adj)
    · decide +kernel
    · intro i mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      subst i
      exact blocked7 adj
end Root17
