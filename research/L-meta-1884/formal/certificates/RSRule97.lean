import RSPin17
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule97 : Rule := ⟨0x20020400080000020000400004000040000000000800001000000000000200000000000000000000000000000000000000000000000,0x400000000000000400000000000000000000000001000000000000200000000000000000000000000000000000000000000000,10,0⟩
private def pg97 : List PetersenPackedPin.Instr := []
private theorem prof97 : Profile p17 pg97 rule97.cover rule97.fixed := certify (by decide +kernel)
theorem okRule97 (adj : Adj) : Correct word tgt rule97 := by
  intro fuel L yes; exact fit_sound (valid17 adj) word_injective prof97 yes
end Root17
