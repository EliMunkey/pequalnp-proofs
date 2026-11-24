import RSPin13
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule90 : Rule := ⟨0x8800020000400080000020000400004000040006004000800001000000000000000800000000000000000000000000000000000000000400,0x800020000400000000020000000000000000002000000000000000000000000000800000000000000000000000000000000000000000000,10,1⟩
private def pg90 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true))]
private theorem prof90 : Profile p13 pg90 rule90.cover rule90.fixed := certify (by decide +kernel)
theorem okRule90 (adj : Adj) : Correct word tgt rule90 := by
  intro fuel L yes; exact fit_sound (valid13 adj) word_injective prof90 yes
end Root17
