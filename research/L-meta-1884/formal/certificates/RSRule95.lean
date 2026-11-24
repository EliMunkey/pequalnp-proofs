import RSPin16
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule95 : Rule := ⟨0x820000400080000020000400004000040000000000800001000000000000800000000000000000000000000000000000000000000000,0x20000000000000000000000004000000000000000000001000000000000800000000000000000000000000000000000000000000000,10,0⟩
private def pg95 : List PetersenPackedPin.Instr := []
private theorem prof95 : Profile p16 pg95 rule95.cover rule95.fixed := certify (by decide +kernel)
theorem okRule95 (adj : Adj) : Correct word tgt rule95 := by
  intro fuel L yes; exact fit_sound (valid16 adj) word_injective prof95 yes
end Root17
