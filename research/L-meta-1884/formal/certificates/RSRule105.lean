import RSPin21
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule105 : Rule := ⟨0x8000820020400080000020000400004000040000004000800001002000000002000000000000000000000000000800000002000000000000,0x8000800020000000000000000400004000000000000000800001002000000000000000000000000000000000000000000000000000000000,7,0⟩
private def pg105 : List PetersenPackedPin.Instr := []
private theorem prof105 : Profile p21 pg105 rule105.cover rule105.fixed := certify (by decide +kernel)
theorem okRule105 (adj : Adj) : Correct word tgt rule105 := by
  intro fuel L yes; exact fit_sound (valid21 adj) word_injective prof105 yes
end Root17
