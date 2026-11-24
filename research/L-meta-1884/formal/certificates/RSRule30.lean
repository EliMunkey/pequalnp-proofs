import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule30 : Rule := ⟨0x802000040008000c021000400004000040000005000840001400400100000400000400040004000400401000400000000000000000000,0x8020000000000004001000000004000000000001000040000400400100000400000400040004000400401000400000000000000000000,12,2⟩
private def pg30 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(3,true))]
private theorem prof30 : Profile p3 pg30 rule30.cover rule30.fixed := certify (by decide +kernel)
theorem okRule30 (adj : Adj) : Correct word tgt rule30 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof30 yes
end Root17
