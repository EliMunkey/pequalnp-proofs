import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule42 : Rule := ⟨0x20000400080000036c00400004000040000204000800001000000000000000080000000000000000000000020000800080002000020,0x36c00000000000000000200000800000000000000000000080000000000000000000000020000800080002000020,12,0⟩
private def pg42 : List PetersenPackedPin.Instr := []
private theorem prof42 : Profile p5 pg42 rule42.cover rule42.fixed := certify (by decide +kernel)
theorem okRule42 (adj : Adj) : Correct word tgt rule42 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof42 yes
end Root17
