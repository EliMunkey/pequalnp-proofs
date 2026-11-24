import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule16 : Rule := ⟨0x80000200004200c48000201006268040000400000045008044011400900208000900000900090008000c0000080210000000840000000050,0x200c48000001006268000000000000005000044001400900208000900000900090008000c0000080210000000840000000050,12,3⟩
private def pg16 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(0,false),(5,true))]
private theorem prof16 : Profile p1 pg16 rule16.cover rule16.fixed := certify (by decide +kernel)
theorem okRule16 (adj : Adj) : Correct word tgt rule16 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof16 yes
end Root17
