import RSPin6
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule53 : Rule := ⟨0xb221a0000400080008020000400004000040000004000000001000000010000000000000000000000000000000000000000200120000000,0x20000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg53 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof53 : Profile p6 pg53 rule53.cover rule53.fixed := certify (by decide +kernel)
theorem okRule53 (adj : Adj) : Correct word tgt rule53 := by
  intro fuel L yes; exact fit_sound (valid6 adj) word_injective prof53 yes
end Root17
