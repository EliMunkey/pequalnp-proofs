import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule11 : Rule := ⟨0x200004000db0010200006d9004000040000504000800001000000000000000140000000000000000180000108001400420005000050,0xdb0010000006d9000000000000500000000000000000000000000140000000000000000180000108001400420005000050,12,0⟩
private def pg11 : List PetersenPackedPin.Instr := []
private theorem prof11 : Profile p1 pg11 rule11.cover rule11.fixed := certify (by decide +kernel)
theorem okRule11 (adj : Adj) : Correct word tgt rule11 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof11 yes
end Root17
