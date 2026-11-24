import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule80 : Rule := ⟨0x120420400080000020000400044000040000004000800001000200000000000000000020080000000000000000000000000100000000,0x44000000000000000000001000000000000000000000000080000000000000000000000000100000000,12,1⟩
private def pg80 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true))]
private theorem prof80 : Profile p10 pg80 rule80.cover rule80.fixed := certify (by decide +kernel)
theorem okRule80 (adj : Adj) : Correct word tgt rule80 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof80 yes
end Root17
