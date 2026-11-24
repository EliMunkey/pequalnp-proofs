import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule21 : Rule := ⟨0x800020000400080000020000400004000040000504000800001000000000000000140000000000000000000000000000000000000000000,0x80000000000400000000000000500000000000000000000000000140000000000000000000000000000000000000000000,12,1⟩
private def pg21 : List PetersenPackedPin.Instr := [(false,(4,true),(3,true))]
private theorem prof21 : Profile p1 pg21 rule21.cover rule21.fixed := certify (by decide +kernel)
theorem okRule21 (adj : Adj) : Correct word tgt rule21 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof21 yes
end Root17
