import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule10 : Rule := ⟨0x8000200004000800000200004000040000400000c4000800001000000000000000030000000000000000000000000000000000000000001,0x40000400000c0000000000000000000000000030000000000000000000000000000000000000000001,12,1⟩
private def pg10 : List PetersenPackedPin.Instr := [(false,(3,true),(4,true))]
private theorem prof10 : Profile p0 pg10 rule10.cover rule10.fixed := certify (by decide +kernel)
theorem okRule10 (adj : Adj) : Correct word tgt rule10 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof10 yes
end Root17
