import RSPin13
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule89 : Rule := ⟨0x800020000400080000020000400004000040002004000800001000000000000000800000000000000000000000000000000000000000000,0x800020000400000000020000000000000000002000000000000000000000000000800000000000000000000000000000000000000000000,10,0⟩
private def pg89 : List PetersenPackedPin.Instr := []
private theorem prof89 : Profile p13 pg89 rule89.cover rule89.fixed := certify (by decide +kernel)
theorem okRule89 (adj : Adj) : Correct word tgt rule89 := by
  intro fuel L yes; exact fit_sound (valid13 adj) word_injective prof89 yes
end Root17
