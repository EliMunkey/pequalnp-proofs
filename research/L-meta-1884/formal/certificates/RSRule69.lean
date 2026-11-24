import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule69 : Rule := ⟨0x20000490880008020000400004000040000004000800001000000000000000000000000000000000000202000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg69 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof69 : Profile p9 pg69 rule69.cover rule69.fixed := certify (by decide +kernel)
theorem okRule69 (adj : Adj) : Correct word tgt rule69 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof69 yes
end Root17
