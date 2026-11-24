import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule3 : Rule := ⟨0x800002000040008000002000040040626c0626e00040c080014103000c00028000c00000800080018003000006000500000001400000000d,0x40626c0626e00000c000014003000c00028000c00000800080018003000006000500000001400000000d,12,3⟩
private def pg3 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(4,true)),(false,(0,false),(6,true))]
private theorem prof3 : Profile p0 pg3 rule3.cover rule3.fixed := certify (by decide +kernel)
theorem okRule3 (adj : Adj) : Correct word tgt rule3 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof3 yes
end Root17
