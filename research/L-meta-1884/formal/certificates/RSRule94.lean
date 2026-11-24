import RSPin15
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule94 : Rule := ⟨0x820000400080000020000400004000040000004000800000000800000000000000000000000000000000000800000000000000000000,0x20000000080000000000000000000000000004000000000000800000000000000000000000000000000000000000000000000000000,10,1⟩
private def pg94 : List PetersenPackedPin.Instr := [(false,(2,true),(0,false))]
private theorem prof94 : Profile p15 pg94 rule94.cover rule94.fixed := certify (by decide +kernel)
theorem okRule94 (adj : Adj) : Correct word tgt rule94 := by
  intro fuel L yes; exact fit_sound (valid15 adj) word_injective prof94 yes
end Root17
