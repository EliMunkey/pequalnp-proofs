import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule71 : Rule := ⟨0x200030020410880000020000400004000040000004000800001000000000000000000000000000000000000802000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg71 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true))]
private theorem prof71 : Profile p9 pg71 rule71.cover rule71.fixed := certify (by decide +kernel)
theorem okRule71 (adj : Adj) : Correct word tgt rule71 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof71 yes
end Root17
