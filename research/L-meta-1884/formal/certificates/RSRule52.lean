import RSPin6
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule52 : Rule := ⟨0x1008080024020440080020260000400004000040000004000800001000000000000000000000000000002201000000000000002000000020000,0x80020000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg52 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(0,false),(5,true))]
private theorem prof52 : Profile p6 pg52 rule52.cover rule52.fixed := certify (by decide +kernel)
theorem okRule52 (adj : Adj) : Correct word tgt rule52 := by
  intro fuel L yes; exact fit_sound (valid6 adj) word_injective prof52 yes
end Root17
