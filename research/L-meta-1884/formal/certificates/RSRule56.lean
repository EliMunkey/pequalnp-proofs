import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule56 : Rule := ⟨0x2020120408080020020000400004000440000004000800001000000000000000000200800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg56 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true))]
private theorem prof56 : Profile p7 pg56 rule56.cover rule56.fixed := certify (by decide +kernel)
theorem okRule56 (adj : Adj) : Correct word tgt rule56 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof56 yes
end Root17
