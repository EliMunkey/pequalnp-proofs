import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule78 : Rule := ⟨0x20000400080108020084400044000040000004000800001000040000000000000000004080008000000000000000000000000000000,0x44000000000000000000001000000000000000000000000080008000000000000000000000000000000,12,1⟩
private def pg78 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof78 : Profile p10 pg78 rule78.cover rule78.fixed := certify (by decide +kernel)
theorem okRule78 (adj : Adj) : Correct word tgt rule78 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof78 yes
end Root17
