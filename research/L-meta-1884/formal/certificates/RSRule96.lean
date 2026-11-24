import RSPin16
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule96 : Rule := ⟨0x820000400080000020000400004000040000000000800001000000000000800000000000000000000000000800000000000000000000,0x20000000000000000000000004000000000000000000001000000000000800000000000000000000000000000000000000000000000,10,1⟩
private def pg96 : List PetersenPackedPin.Instr := [(false,(2,true),(0,false))]
private theorem prof96 : Profile p16 pg96 rule96.cover rule96.fixed := certify (by decide +kernel)
theorem okRule96 (adj : Adj) : Correct word tgt rule96 := by
  intro fuel L yes; exact fit_sound (valid16 adj) word_injective prof96 yes
end Root17
