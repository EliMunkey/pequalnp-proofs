import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule28 : Rule := ⟨0x800020010400080004020000400004000040001005000800001400000000000000400000000000000000400000000002000000900000000,0x20010000000004000000000004000000001001000000000400000000000000400000000000000000400000000002000000000000000,12,0⟩
private def pg28 : List PetersenPackedPin.Instr := []
private theorem prof28 : Profile p3 pg28 rule28.cover rule28.fixed := certify (by decide +kernel)
theorem okRule28 (adj : Adj) : Correct word tgt rule28 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof28 yes
end Root17
