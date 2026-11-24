import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule61 : Rule := ⟨0x4820080408080000020040400004000440000004000800001000000000000000000800800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg61 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true))]
private theorem prof61 : Profile p7 pg61 rule61.cover rule61.fixed := certify (by decide +kernel)
theorem okRule61 (adj : Adj) : Correct word tgt rule61 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof61 yes
end Root17
