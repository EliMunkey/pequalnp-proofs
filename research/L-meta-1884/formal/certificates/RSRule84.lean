import RSPin11
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule84 : Rule := ⟨0x20020000400080200020030400004000040004004000800001000000000000000000000000000040000000000000000000000000000000,0x400000000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,0⟩
private def pg84 : List PetersenPackedPin.Instr := []
private theorem prof84 : Profile p11 pg84 rule84.cover rule84.fixed := certify (by decide +kernel)
theorem okRule84 (adj : Adj) : Correct word tgt rule84 := by
  intro fuel L yes; exact fit_sound (valid11 adj) word_injective prof84 yes
end Root17
