import RSIndex
import RSRules
import PetersenPairHints
open PetersenWordCost PetersenLayerCheck PetersenBank PetersenPackedPin
namespace Root17
set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
def nextf1 : Array Nat := #[4,6,1,2]
def hintsf1 : List Nat := [4106,16405,4106,0,1031,2055,1031,1,7,2055,4106,2,7,16405,1031,3]
theorem pair1 (adj : Adj) : PetersenRootOrbit.DeadPair tgt 16 primary.toFinset (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : W) (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc : W) := by
  apply PetersenPairHints.killed (nxt := nextf1.map live) (hs := hintsf1)
  · decide +kernel
  · apply PetersenRuleBank.children (tab := rules) (which := whichRule) (ids := ids) (more := []) (ok := validRules adj)
    · decide +kernel
    · intro i mem
      simp at mem
end Root17
