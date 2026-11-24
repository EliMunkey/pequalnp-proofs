import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule76 : Rule := ⟨0x820002400080000020004400004000040000004000800001000800000000000000000000000008000000000000040000000000000000,0x4000000000000000000001000000000000000000000000000008000000000000040000000000000000,12,1⟩
private def pg76 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true))]
private theorem prof76 : Profile p10 pg76 rule76.cover rule76.fixed := certify (by decide +kernel)
theorem okRule76 (adj : Adj) : Correct word tgt rule76 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof76 yes
end Root17
