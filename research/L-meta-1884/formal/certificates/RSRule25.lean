import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule25 : Rule := ⟨0x2080050008000a020200400004000040000004808000001200100014000100000100010001000100200400000000001000000000000,0x800500000002000200400000000000000000808000000200100004000100000100010001000100200400000000001000000000000,12,3⟩
private def pg25 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(3,true)),(false,(3,true),(0,true))]
private theorem prof25 : Profile p2 pg25 rule25.cover rule25.fixed := certify (by decide +kernel)
theorem okRule25 (adj : Adj) : Correct word tgt rule25 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof25 yes
end Root17
