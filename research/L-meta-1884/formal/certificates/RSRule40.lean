import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule40 : Rule := ⟨0x420064403080000c200004000040018400080042218a101100c00308101822300000300000000000600000c000000082000250000000,0x80042008a101000c00300001000200000300000000000600000c000000080000200000000,12,2⟩
private def pg40 : List PetersenPackedPin.Instr := [(false,(0,true),(7,true)),(false,(0,true),(7,true))]
private theorem prof40 : Profile p4 pg40 rule40.cover rule40.fixed := certify (by decide +kernel)
theorem okRule40 (adj : Adj) : Correct word tgt rule40 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof40 yes
end Root17
