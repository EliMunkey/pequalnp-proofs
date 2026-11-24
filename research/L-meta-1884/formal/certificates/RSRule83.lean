import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule83 : Rule := ⟨0x1800020000400080000020000400004000040004004000800001801000000000001000000000000000000000000000000000000000000080,0x4000000000000000000001800000000000001000000000000000000000000000000000000000000080,12,1⟩
private def pg83 : List PetersenPackedPin.Instr := [(false,(7,true),(3,true))]
private theorem prof83 : Profile p10 pg83 rule83.cover rule83.fixed := certify (by decide +kernel)
theorem okRule83 (adj : Adj) : Correct word tgt rule83 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof83 yes
end Root17
