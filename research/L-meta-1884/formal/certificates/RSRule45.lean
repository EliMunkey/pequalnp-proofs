import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule45 : Rule := ⟨0x820000400080000024400400004000040000004000800001080020000000000000020000000000000000100820000000000002000000,0x24400000000000000000000000800000080020000000000000020000000000000000100020000000000002000000,12,3⟩
private def pg45 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true)),(false,(0,false),(3,true)),(false,(5,true),(0,true))]
private theorem prof45 : Profile p5 pg45 rule45.cover rule45.fixed := certify (by decide +kernel)
theorem okRule45 (adj : Adj) : Correct word tgt rule45 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof45 yes
end Root17
