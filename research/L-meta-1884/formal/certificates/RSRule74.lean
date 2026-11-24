import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule74 : Rule := ⟨0x2000800028000404880000020000400004000040004004000800001000000000000000000000000000000000004012000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg74 : List PetersenPackedPin.Instr := [(false,(7,true),(3,true))]
private theorem prof74 : Profile p9 pg74 rule74.cover rule74.fixed := certify (by decide +kernel)
theorem okRule74 (adj : Adj) : Correct word tgt rule74 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof74 yes
end Root17
