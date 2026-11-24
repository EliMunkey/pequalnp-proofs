import RSPin18
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule99 : Rule := ⟨0x20000400080008020000400004000040000000000800001000000010000040004000000000000000000000000000000000000000000,0x20000000000000000000000000800001000000000000040004000000000000000000000000000000000000000000,10,0⟩
private def pg99 : List PetersenPackedPin.Instr := []
private theorem prof99 : Profile p18 pg99 rule99.cover rule99.fixed := certify (by decide +kernel)
theorem okRule99 (adj : Adj) : Correct word tgt rule99 := by
  intro fuel L yes; exact fit_sound (valid18 adj) word_injective prof99 yes
end Root17
