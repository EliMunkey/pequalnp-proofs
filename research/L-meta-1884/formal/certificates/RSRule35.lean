import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule35 : Rule := ⟨0x62000c403080018f2001840018400184000c02422080301900c00301101806300400300030003000601000c000300000000c00000000,0x800420080301000c00300001000200000300030003000601000c000300000000c00000000,12,1⟩
private def pg35 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true))]
private theorem prof35 : Profile p4 pg35 rule35.cover rule35.fixed := certify (by decide +kernel)
theorem okRule35 (adj : Adj) : Correct word tgt rule35 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof35 yes
end Root17
