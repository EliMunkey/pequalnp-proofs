import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule8 : Rule := ⟨0x2000040008000802000040040427c0427e00040c000028103000c01014000c000008000800180030060060005000000014000000001,0x40427c0427e00000c000028003000c00014000c000008000800180030060060005000000014000000001,12,3⟩
private def pg8 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(7,true)),(false,(3,true),(0,true))]
private theorem prof8 : Profile p0 pg8 rule8.cover rule8.fixed := certify (by decide +kernel)
theorem okRule8 (adj : Adj) : Correct word tgt rule8 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof8 yes
end Root17
