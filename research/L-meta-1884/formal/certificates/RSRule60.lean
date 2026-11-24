import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule60 : Rule := ⟨0x20080408080048020040400004000640000004000000001000000010000000000040c00000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg60 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof60 : Profile p7 pg60 rule60.cover rule60.fixed := certify (by decide +kernel)
theorem okRule60 (adj : Adj) : Correct word tgt rule60 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof60 yes
end Root17
