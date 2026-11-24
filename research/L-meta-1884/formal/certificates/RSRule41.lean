import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule41 : Rule := ⟨0x6800020000403080000c2000040000400184001c006220a0103100c00340103902300800300000000000600000c000000000000000000300,0x8006200a0103000c00300001000200800300000000000600000c000000000000000000300,12,1⟩
private def pg41 : List PetersenPackedPin.Instr := [(false,(7,true),(6,true))]
private theorem prof41 : Profile p4 pg41 rule41.cover rule41.fixed := certify (by decide +kernel)
theorem okRule41 (adj : Adj) : Correct word tgt rule41 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof41 yes
end Root17
