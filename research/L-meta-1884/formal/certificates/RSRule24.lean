import RSPin2
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule24 : Rule := ⟨0x2080050008000a020200400004000040000004800808001200100040000100000100010001000100200400000000001000000000000,0x800500000002000200400000000000000000800008000200100040000100000100010001000100200400000000001000000000000,12,2⟩
private def pg24 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(3,true))]
private theorem prof24 : Profile p2 pg24 rule24.cover rule24.fixed := certify (by decide +kernel)
theorem okRule24 (adj : Adj) : Correct word tgt rule24 := by
  intro fuel L yes; exact fit_sound (valid2 adj) word_injective prof24 yes
end Root17
