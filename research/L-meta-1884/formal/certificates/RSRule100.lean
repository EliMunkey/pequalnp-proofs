import RSPin19
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule100 : Rule := ⟨0x20000400080008020000400004000040000004000800000000040010004000000000000000000000000000000000000000000000000,0x20000000000000000000004000800000000040000004000000000000000000000000000000000000000000000000,10,0⟩
private def pg100 : List PetersenPackedPin.Instr := []
private theorem prof100 : Profile p19 pg100 rule100.cover rule100.fixed := certify (by decide +kernel)
theorem okRule100 (adj : Adj) : Correct word tgt rule100 := by
  intro fuel L yes; exact fit_sound (valid19 adj) word_injective prof100 yes
end Root17
