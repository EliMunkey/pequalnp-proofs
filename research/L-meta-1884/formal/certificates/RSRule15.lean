import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule15 : Rule := ⟨0x2002042008e8000201004768040000400000045008044011400900208000900000900090008000c0000080210001400c60000000000,0x2008e8000001004768000000000000005000044001400900208000900000900090008000c0000080210001400c60000000000,12,2⟩
private def pg15 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(5,true))]
private theorem prof15 : Profile p1 pg15 rule15.cover rule15.fixed := certify (by decide +kernel)
theorem okRule15 (adj : Adj) : Correct word tgt rule15 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof15 yes
end Root17
