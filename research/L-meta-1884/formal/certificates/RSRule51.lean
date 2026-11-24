import RSPin6
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule51 : Rule := ⟨0x800ba2922000440080228220000400004000040004004000800001000000000000000000000000000001809000000000000000200100000000,0x80020000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg51 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof51 : Profile p6 pg51 rule51.cover rule51.fixed := certify (by decide +kernel)
theorem okRule51 (adj : Adj) : Correct word tgt rule51 := by
  intro fuel L yes; exact fit_sound (valid6 adj) word_injective prof51 yes
end Root17
