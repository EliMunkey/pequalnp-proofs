import RSPin12
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule88 : Rule := ⟨0x20000400080000020000400004000040000004020800001000000000000000000000000000000000000000000000000000000000000,0x20800001000000000000000000000000000000000000000000000000000000000000,12,0⟩
private def pg88 : List PetersenPackedPin.Instr := []
private theorem prof88 : Profile p12 pg88 rule88.cover rule88.fixed := certify (by decide +kernel)
theorem okRule88 (adj : Adj) : Correct word tgt rule88 := by
  intro fuel L yes; exact fit_sound (valid12 adj) word_injective prof88 yes
end Root17
