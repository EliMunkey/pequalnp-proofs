import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule82 : Rule := ⟨0x120020400080000020000400004000040000004000800001000200000000000000000000000000000000000000000002000080000000,0x4000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg82 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true)),(false,(0,true),(4,true))]
private theorem prof82 : Profile p10 pg82 rule82.cover rule82.fixed := certify (by decide +kernel)
theorem okRule82 (adj : Adj) : Correct word tgt rule82 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof82 yes
end Root17
