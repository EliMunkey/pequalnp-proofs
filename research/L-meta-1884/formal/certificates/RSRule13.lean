import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule13 : Rule := ⟨0x8200004200958000201004ae8040000400000045008044011400900208000900000900090008000c0000080318000000840005000000,0x200958000001004ae8000000000000005000044001400900208000900000900090008000c0000080318000000840005000000,12,2⟩
private def pg13 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(4,true))]
private theorem prof13 : Profile p1 pg13 rule13.cover rule13.fixed := certify (by decide +kernel)
theorem okRule13 (adj : Adj) : Correct word tgt rule13 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof13 yes
end Root17
