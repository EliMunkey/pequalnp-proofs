import RSPin11
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule85 : Rule := ⟨0x20000400080408020000400004000040000004000800001000000000000000000000000000400000000000000000000000000000000,0x400000000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg85 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof85 : Profile p11 pg85 rule85.cover rule85.fixed := certify (by decide +kernel)
theorem okRule85 (adj : Adj) : Correct word tgt rule85 := by
  intro fuel L yes; exact fit_sound (valid11 adj) word_injective prof85 yes
end Root17
