import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule29 : Rule := ⟨0x80abaf202004100800800210804003c40000400050050008400014004001000004004004001c2784000400001000400000000101d00000000,0x8020000000000000001000000004000000001001000040000400400100000400400400040004000400001000400000000000000000000,12,1⟩
private def pg29 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true))]
private theorem prof29 : Profile p3 pg29 rule29.cover rule29.fixed := certify (by decide +kernel)
theorem okRule29 (adj : Adj) : Correct word tgt rule29 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof29 yes
end Root17
