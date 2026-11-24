import RSPin20
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule102 : Rule := ⟨0x20020000080000020000400004000040000004000800001000000000000000000000000000000000000000000400002000000000000,0x4000800001000000000000000000000000000000000000000000400000000000000000,10,1⟩
private def pg102 : List PetersenPackedPin.Instr := [(false,(0,false),(2,true))]
private theorem prof102 : Profile p20 pg102 rule102.cover rule102.fixed := certify (by decide +kernel)
theorem okRule102 (adj : Adj) : Correct word tgt rule102 := by
  intro fuel L yes; exact fit_sound (valid20 adj) word_injective prof102 yes
end Root17
