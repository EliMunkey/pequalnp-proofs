import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule59 : Rule := ⟨0x20080408080048020040400004000440000004000800001000000000000000000040800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg59 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof59 : Profile p7 pg59 rule59.cover rule59.fixed := certify (by decide +kernel)
theorem okRule59 (adj : Adj) : Correct word tgt rule59 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof59 yes
end Root17
