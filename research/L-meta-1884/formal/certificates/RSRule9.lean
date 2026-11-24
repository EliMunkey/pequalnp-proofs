import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule9 : Rule := ⟨0x80002000040008000002000040040526c0526e40c40c080014103000c00028000c030008000800180030000060005000000014000001801,0x40526c0526e00c00c000014003000c00028000c030008000800180030000060005000000014000001801,12,2⟩
private def pg9 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(4,true),(5,true))]
private theorem prof9 : Profile p0 pg9 rule9.cover rule9.fixed := certify (by decide +kernel)
theorem okRule9 (adj : Adj) : Correct word tgt rule9 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof9 yes
end Root17
