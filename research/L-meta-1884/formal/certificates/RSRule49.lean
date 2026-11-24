import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule49 : Rule := ⟨0x800020000400080000028000400004000040004204000800001080020000000000080020000000000000000100000000000000000004000,0x28000000000000000000200000800000080020000000000080020000000000000000100000000000000000004000,12,2⟩
private def pg49 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true)),(false,(4,true),(3,true))]
private theorem prof49 : Profile p5 pg49 rule49.cover rule49.fixed := certify (by decide +kernel)
theorem okRule49 (adj : Adj) : Correct word tgt rule49 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof49 yes
end Root17
