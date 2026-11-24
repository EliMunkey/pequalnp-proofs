import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule77 : Rule := ⟨0x820002400080000020000400004000040000004000800001000800000000000000000000000000000000000800020000000000000000,0x4000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg77 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true)),(false,(8,true),(0,true))]
private theorem prof77 : Profile p10 pg77 rule77.cover rule77.fixed := certify (by decide +kernel)
theorem okRule77 (adj : Adj) : Correct word tgt rule77 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof77 yes
end Root17
