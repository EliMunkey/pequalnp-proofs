import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule50 : Rule := ⟨0x800020000400080000020000400004000040000204000800001000000000000000080000000000000000000000000000000000000000000,0x20000000000000000000200000800000000000000000000080000000000000000000000000000000000000000000,12,1⟩
private def pg50 : List PetersenPackedPin.Instr := [(false,(3,true),(2,true))]
private theorem prof50 : Profile p5 pg50 rule50.cover rule50.fixed := certify (by decide +kernel)
theorem okRule50 (adj : Adj) : Correct word tgt rule50 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof50 yes
end Root17
