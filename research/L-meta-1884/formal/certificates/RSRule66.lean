import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule66 : Rule := ⟨0x200028000454880000020000400004000040004004000800001000000000000000000000000000000000000012000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,0⟩
private def pg66 : List PetersenPackedPin.Instr := []
private theorem prof66 : Profile p9 pg66 rule66.cover rule66.fixed := certify (by decide +kernel)
theorem okRule66 (adj : Adj) : Correct word tgt rule66 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof66 yes
end Root17
