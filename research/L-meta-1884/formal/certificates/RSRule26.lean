import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule26 : Rule := ⟨0x40886086aa8e7000802000202dd40000400004000401480080800520010004000010000010001002d238100000400c40340011000008000000,0x800700000000000200400000000000000000800008000200100040000100000100010001000100000400000000001000008000000,12,2⟩
private def pg26 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(8,true))]
private theorem prof26 : Profile p2 pg26 rule26.cover rule26.fixed := certify (by decide +kernel)
theorem okRule26 (adj : Adj) : Correct word tgt rule26 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof26 yes
end Root17
