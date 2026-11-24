import RSPin14
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule91 : Rule := ⟨0x20020400080000020000400004000040000004000800000000200000000000000000000000000000000000000000000000000000000,0x400000000000000000000000040000004000000000000200000000000000000000000000000000000000000000000000000000,10,0⟩
private def pg91 : List PetersenPackedPin.Instr := []
private theorem prof91 : Profile p14 pg91 rule91.cover rule91.fixed := certify (by decide +kernel)
theorem okRule91 (adj : Adj) : Correct word tgt rule91 := by
  intro fuel L yes; exact fit_sound (valid14 adj) word_injective prof91 yes
end Root17
