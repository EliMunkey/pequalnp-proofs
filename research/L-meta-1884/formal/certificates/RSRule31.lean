import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule31 : Rule := ⟨0x802000040008000c021000400004000040000005010000001400400018000400000400040004000400401000400000000000000000000,0x8020000000000004001000000004000000000001010000000400400008000400000400040004000400401000400000000000000000000,12,3⟩
private def pg31 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(3,true)),(false,(3,true),(0,true))]
private theorem prof31 : Profile p3 pg31 rule31.cover rule31.fixed := certify (by decide +kernel)
theorem okRule31 (adj : Adj) : Correct word tgt rule31 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof31 yes
end Root17
