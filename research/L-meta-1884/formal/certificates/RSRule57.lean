import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule57 : Rule := ⟨0x48000020000408080000020000400004000440000004000800001000000000000000002000800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg57 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true)),(false,(0,false),(8,true))]
private theorem prof57 : Profile p7 pg57 rule57.cover rule57.fixed := certify (by decide +kernel)
theorem okRule57 (adj : Adj) : Correct word tgt rule57 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof57 yes
end Root17
