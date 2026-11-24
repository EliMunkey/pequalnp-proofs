import RSPin14
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule92 : Rule := ⟨0x20020400080000020000400004000040000004000800000000200000000000000000000000000000000000000000002000000000000,0x400000000000000000000000040000004000000000000200000000000000000000000000000000000000000000000000000000,10,1⟩
private def pg92 : List PetersenPackedPin.Instr := [(false,(0,false),(2,true))]
private theorem prof92 : Profile p14 pg92 rule92.cover rule92.fixed := certify (by decide +kernel)
theorem okRule92 (adj : Adj) : Correct word tgt rule92 := by
  intro fuel L yes; exact fit_sound (valid14 adj) word_injective prof92 yes
end Root17
