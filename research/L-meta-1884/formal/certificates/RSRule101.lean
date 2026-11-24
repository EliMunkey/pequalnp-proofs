import RSPin20
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule101 : Rule := ⟨0x820020400080008020000400004000040004004000800001000000010000000000000000000000008800000000400000001000000400,0x4004000800001000000000000000000000000000000008800000000400000001000000400,10,0⟩
private def pg101 : List PetersenPackedPin.Instr := []
private theorem prof101 : Profile p20 pg101 rule101.cover rule101.fixed := certify (by decide +kernel)
theorem okRule101 (adj : Adj) : Correct word tgt rule101 := by
  intro fuel L yes; exact fit_sound (valid20 adj) word_injective prof101 yes
end Root17
