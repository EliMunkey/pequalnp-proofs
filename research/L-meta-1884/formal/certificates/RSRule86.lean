import RSPin11
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule86 : Rule := ⟨0x20000400080408020002400004000040000004000000001000000010000000000000000000404000000000000000000000000000000,0x400000000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg86 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof86 : Profile p11 pg86 rule86.cover rule86.fixed := certify (by decide +kernel)
theorem okRule86 (adj : Adj) : Correct word tgt rule86 := by
  intro fuel L yes; exact fit_sound (valid11 adj) word_injective prof86 yes
end Root17
