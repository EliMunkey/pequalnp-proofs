import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule38 : Rule := ⟨0x620064403080000c200004001840018400080042208a101100c00308101822300000300030000000600000c000000080000e00000000,0x80042008a101000c00300001000200000300030000000600000c000000080000e00000000,12,1⟩
private def pg38 : List PetersenPackedPin.Instr := [(false,(0,true),(7,true))]
private theorem prof38 : Profile p4 pg38 rule38.cover rule38.fixed := certify (by decide +kernel)
theorem okRule38 (adj : Adj) : Correct word tgt rule38 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof38 yes
end Root17
