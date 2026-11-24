import RSPin8
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule65 : Rule := ⟨0x2c203400080008020000400004000040000004000000001000000010000000000000000000000000000000080048000000000000000,0x400000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg65 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof65 : Profile p8 pg65 rule65.cover rule65.fixed := certify (by decide +kernel)
theorem okRule65 (adj : Adj) : Correct word tgt rule65 := by
  intro fuel L yes; exact fit_sound (valid8 adj) word_injective prof65 yes
end Root17
