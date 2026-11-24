import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule48 : Rule := ⟨0x20020400080000022800400004000040000004000800001080020000000000000020000000000000000100000000802080000000000,0x22800000000000000000000000800000080020000000000000020000000000000000100000000800080000000000,12,3⟩
private def pg48 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true)),(false,(0,false),(4,true)),(false,(0,true),(4,true))]
private theorem prof48 : Profile p5 pg48 rule48.cover rule48.fixed := certify (by decide +kernel)
theorem okRule48 (adj : Adj) : Correct word tgt rule48 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof48 yes
end Root17
