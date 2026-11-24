import RSPin20
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule103 : Rule := ⟨0x800000400080000020000400004000040000004000800001000000000000000000000000000000000000000800000000001000000000,0x4000800001000000000000000000000000000000000000000000000000001000000000,10,1⟩
private def pg103 : List PetersenPackedPin.Instr := [(false,(0,true),(2,false))]
private theorem prof103 : Profile p20 pg103 rule103.cover rule103.fixed := certify (by decide +kernel)
theorem okRule103 (adj : Adj) : Correct word tgt rule103 := by
  intro fuel L yes; exact fit_sound (valid20 adj) word_injective prof103 yes
end Root17
