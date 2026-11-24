import RSPin6
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule54 : Rule := ⟨0x1008200004400800202a0000400004000040000004000800001000000000000000000000000000000801000000800000008000000000000,0x20000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg54 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(5,true),(0,true))]
private theorem prof54 : Profile p6 pg54 rule54.cover rule54.fixed := certify (by decide +kernel)
theorem okRule54 (adj : Adj) : Correct word tgt rule54 := by
  intro fuel L yes; exact fit_sound (valid6 adj) word_injective prof54 yes
end Root17
