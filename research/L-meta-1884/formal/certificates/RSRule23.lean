import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule23 : Rule := ⟨0x20082002baae5000802000202fc400004000040004804800808001200100040000100200100010017278100000400440740001000000000000,0x800500000000000200400000000000000800800008000200100040000100200100010001000100000400000000001000000000000,12,1⟩
private def pg23 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true))]
private theorem prof23 : Profile p2 pg23 rule23.cover rule23.fixed := certify (by decide +kernel)
theorem okRule23 (adj : Adj) : Correct word tgt rule23 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof23 yes
end Root17
