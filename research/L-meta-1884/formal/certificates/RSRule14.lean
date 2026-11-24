import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule14 : Rule := ⟨0x8200004200958000201004ae8040000400000045008044011400900208000900000900090008000c0000080b18000000840005000000,0x200958000001004ae8000000000000005000044001400900208000900000900090008000c0000080318000000840005000000,12,3⟩
private def pg14 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(4,true)),(false,(6,true),(0,true))]
private theorem prof14 : Profile p1 pg14 rule14.cover rule14.fixed := certify (by decide +kernel)
theorem okRule14 (adj : Adj) : Correct word tgt rule14 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof14 yes
end Root17
