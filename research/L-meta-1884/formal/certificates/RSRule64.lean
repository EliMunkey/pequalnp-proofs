import RSPin8
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule64 : Rule := ⟨0x2e222440080088220000400004000040004004000800001000000000000000000000000000000201000000080040000000000000000,0x2000400000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg64 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true))]
private theorem prof64 : Profile p8 pg64 rule64.cover rule64.fixed := certify (by decide +kernel)
theorem okRule64 (adj : Adj) : Correct word tgt rule64 := by
  intro fuel L yes; exact fit_sound (valid8 adj) word_injective prof64 yes
end Root17
