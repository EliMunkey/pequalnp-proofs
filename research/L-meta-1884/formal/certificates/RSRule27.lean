import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule27 : Rule := ⟨0x82002baaed000802000202dcc00004000040004004800808001200100040000100000100010007238100000400440740003000000040400,0x800500000000000200400000000000000000800008000200100040000100000100010001000100000400000000001000000000000,12,2⟩
private def pg27 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,true),(8,true))]
private theorem prof27 : Profile p2 pg27 rule27.cover rule27.fixed := certify (by decide +kernel)
theorem okRule27 (adj : Adj) : Correct word tgt rule27 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof27 yes
end Root17
