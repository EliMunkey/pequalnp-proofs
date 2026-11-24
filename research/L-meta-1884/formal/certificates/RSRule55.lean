import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule55 : Rule := ⟨0x2020080408080020020040400004002440004004000800001000000000000000000004800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,0⟩
private def pg55 : List PetersenPackedPin.Instr := []
private theorem prof55 : Profile p7 pg55 rule55.cover rule55.fixed := certify (by decide +kernel)
theorem okRule55 (adj : Adj) : Correct word tgt rule55 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof55 yes
end Root17
