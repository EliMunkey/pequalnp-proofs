import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule22 : Rule := ⟨0x800020000700080002020000400004000040000804800800001200000000000000200000000000000000200000400240001000008000000,0x700000002000000400000000000000800800000000200000000000000200000000000000000200000000000001000008000000,12,0⟩
private def pg22 : List PetersenPackedPin.Instr := []
private theorem prof22 : Profile p2 pg22 rule22.cover rule22.fixed := certify (by decide +kernel)
theorem okRule22 (adj : Adj) : Correct word tgt rule22 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof22 yes
end Root17
