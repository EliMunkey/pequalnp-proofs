import RSPin17
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule98 : Rule := ⟨0x20020400080000020000400004000040000000000800001000000000000200000000000000000000000000000000002000000000000,0x400000000000000400000000000000000000000001000000000000200000000000000000000000000000000000000000000000,10,1⟩
private def pg98 : List PetersenPackedPin.Instr := [(false,(0,false),(2,true))]
private theorem prof98 : Profile p17 pg98 rule98.cover rule98.fixed := certify (by decide +kernel)
theorem okRule98 (adj : Adj) : Correct word tgt rule98 := by
  intro fuel L yes; exact fit_sound (valid17 adj) word_injective prof98 yes
end Root17
