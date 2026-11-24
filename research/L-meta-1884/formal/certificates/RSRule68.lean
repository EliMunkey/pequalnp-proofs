import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule68 : Rule := ⟨0x400820000400a80000020000400004000040000004000800001000000000000000000000000000000000002002800000004000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg68 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true)),(false,(8,true),(0,true))]
private theorem prof68 : Profile p9 pg68 rule68.cover rule68.fixed := certify (by decide +kernel)
theorem okRule68 (adj : Adj) : Correct word tgt rule68 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof68 yes
end Root17
