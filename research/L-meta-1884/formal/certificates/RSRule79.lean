import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule79 : Rule := ⟨0x200004000801080200844000640000400000040000000010000400100040000000000040c0008000000000000000000000000000000,0x44000000000000000000001000000000000000000000000080008000000000000000000000000000000,12,2⟩
private def pg79 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof79 : Profile p10 pg79 rule79.cover rule79.fixed := certify (by decide +kernel)
theorem okRule79 (adj : Adj) : Correct word tgt rule79 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof79 yes
end Root17
