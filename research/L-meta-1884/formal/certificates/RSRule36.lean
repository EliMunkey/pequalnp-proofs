import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule36 : Rule := ⟨0x1a2000c403080000c2001840000400184000800422091101100c00320101882300000300000003000600000c000380000000000200000,0x800420091101000c00300001000200000300000003000600000c000380000000000200000,12,1⟩
private def pg36 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true))]
private theorem prof36 : Profile p4 pg36 rule36.cover rule36.fixed := certify (by decide +kernel)
theorem okRule36 (adj : Adj) : Correct word tgt rule36 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof36 yes
end Root17
