import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule43 : Rule := ⟨0x800220004400802a8028000400004000040004204000800001080020010000000080020002000200009800100040000000100000004000,0x28000000000000000000200000800000080020000000000080020002000200000000100040000000100000004000,12,1⟩
private def pg43 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true))]
private theorem prof43 : Profile p5 pg43 rule43.cover rule43.fixed := certify (by decide +kernel)
theorem okRule43 (adj : Adj) : Correct word tgt rule43 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof43 yes
end Root17
