import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule34 : Rule := ⟨0x62000c403080000c2001840018400184001c006220fb303100c00300103802300800300030003000601000c000380080000e00200302,0x8006200fb303000c00300001000200800300030003000601000c000380080000e00200302,12,0⟩
private def pg34 : List PetersenPackedPin.Instr := []
private theorem prof34 : Profile p4 pg34 rule34.cover rule34.fixed := certify (by decide +kernel)
theorem okRule34 (adj : Adj) : Correct word tgt rule34 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof34 yes
end Root17
