import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule67 : Rule := ⟨0x400828000400880000020000400004000040000004000800001000000000000000000000000000000000002002000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg67 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true))]
private theorem prof67 : Profile p9 pg67 rule67.cover rule67.fixed := certify (by decide +kernel)
theorem okRule67 (adj : Adj) : Correct word tgt rule67 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof67 yes
end Root17
