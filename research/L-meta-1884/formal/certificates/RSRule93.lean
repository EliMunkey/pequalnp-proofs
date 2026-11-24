import RSPin15
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule93 : Rule := ⟨0x820000400080000020000400004000040000004000800000000800000000000000000000000000000000000000000000000000000000,0x20000000080000000000000000000000000004000000000000800000000000000000000000000000000000000000000000000000000,10,0⟩
private def pg93 : List PetersenPackedPin.Instr := []
private theorem prof93 : Profile p15 pg93 rule93.cover rule93.fixed := certify (by decide +kernel)
theorem okRule93 (adj : Adj) : Correct word tgt rule93 := by
  intro fuel L yes; exact fit_sound (valid15 adj) word_injective prof93 yes
end Root17
