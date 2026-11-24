import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule75 : Rule := ⟨0x120202400080080220084400344000040004004000800001800000000008001000000000480008001000000000040000000100000080,0x44000000000000000000001800000000008001000000000080008001000000000040000000100000080,12,0⟩
private def pg75 : List PetersenPackedPin.Instr := []
private theorem prof75 : Profile p10 pg75 rule75.cover rule75.fixed := certify (by decide +kernel)
theorem okRule75 (adj : Adj) : Correct word tgt rule75 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof75 yes
end Root17
