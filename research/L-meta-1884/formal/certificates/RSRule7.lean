import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule7 : Rule := ⟨0x2000040008000802000040040427c0427e00040c080014103000c00028000c000008000800180030060060005000000014000000001,0x40427c0427e00000c000014003000c00028000c000008000800180030060060005000000014000000001,12,2⟩
private def pg7 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(7,true))]
private theorem prof7 : Profile p0 pg7 rule7.cover rule7.fixed := certify (by decide +kernel)
theorem okRule7 (adj : Adj) : Correct word tgt rule7 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof7 yes
end Root17
