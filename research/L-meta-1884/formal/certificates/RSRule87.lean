import RSPin11
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule87 : Rule := ⟨0x40820000400080000020000400004000040000004000800001000000000000000000000000008000000000000000000000000000000000,0x400000000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg87 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true))]
private theorem prof87 : Profile p11 pg87 rule87.cover rule87.fixed := certify (by decide +kernel)
theorem okRule87 (adj : Adj) : Correct word tgt rule87 := by
  intro fuel L yes; exact fit_sound (valid11 adj) word_injective prof87 yes
end Root17
