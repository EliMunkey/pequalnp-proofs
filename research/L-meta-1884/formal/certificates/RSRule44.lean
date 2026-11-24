import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule44 : Rule := ⟨0x820000400080000024400400004000040000004000800001080020000000000000020000000200000000100060000000000002000000,0x24400000000000000000000000800000080020000000000000020000000200000000100060000000000002000000,12,2⟩
private def pg44 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true)),(false,(0,false),(3,true))]
private theorem prof44 : Profile p5 pg44 rule44.cover rule44.fixed := certify (by decide +kernel)
theorem okRule44 (adj : Adj) : Correct word tgt rule44 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof44 yes
end Root17
