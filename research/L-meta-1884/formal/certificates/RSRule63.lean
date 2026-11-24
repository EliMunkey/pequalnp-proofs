import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule63 : Rule := ⟨0x20802020000408080000020000400004002440004004000800001000000000000000001004800000000000000000000000000000000000000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,1⟩
private def pg63 : List PetersenPackedPin.Instr := [(false,(3,true),(7,true))]
private theorem prof63 : Profile p7 pg63 rule63.cover rule63.fixed := certify (by decide +kernel)
theorem okRule63 (adj : Adj) : Correct word tgt rule63 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof63 yes
end Root17
