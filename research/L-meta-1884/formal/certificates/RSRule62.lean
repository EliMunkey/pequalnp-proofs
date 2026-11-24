import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule62 : Rule := ⟨0x4820000408080000020000400004000540000004000800001000000000000000000800800000000000000000800000040000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg62 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true)),(false,(4,true),(0,true))]
private theorem prof62 : Profile p7 pg62 rule62.cover rule62.fixed := certify (by decide +kernel)
theorem okRule62 (adj : Adj) : Correct word tgt rule62 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof62 yes
end Root17
