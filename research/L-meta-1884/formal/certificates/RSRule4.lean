import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule4 : Rule := ⟨0x2002040008000002000040040476c0476e00040c080014103000c00028000c00000800080018003000006000500030201e000000001,0x40476c0476e00000c000014003000c00028000c00000800080018003000006000500030001e000000001,12,3⟩
private def pg4 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(4,true)),(false,(0,true),(6,true))]
private theorem prof4 : Profile p0 pg4 rule4.cover rule4.fixed := certify (by decide +kernel)
theorem okRule4 (adj : Adj) : Correct word tgt rule4 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof4 yes
end Root17
