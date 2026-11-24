import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule73 : Rule := ⟨0x30020400980000020000400004000040000004000800001000000000000000000000000000000000000802000000002000000010000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg73 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true)),(false,(0,true),(4,true))]
private theorem prof73 : Profile p9 pg73 rule73.cover rule73.fixed := certify (by decide +kernel)
theorem okRule73 (adj : Adj) : Correct word tgt rule73 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof73 yes
end Root17
