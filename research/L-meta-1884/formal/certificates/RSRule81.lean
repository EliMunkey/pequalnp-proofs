import RSPin10
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule81 : Rule := ⟨0x8000020000400080000020000400004000040000004000800001002000000000000000000000000000000000000000000000000000000000,0x4000000000000000000001000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg81 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true)),(false,(0,false),(4,true))]
private theorem prof81 : Profile p10 pg81 rule81.cover rule81.fixed := certify (by decide +kernel)
theorem okRule81 (adj : Adj) : Correct word tgt rule81 := by
  intro fuel L yes; exact fit_sound (valid10 adj) word_injective prof81 yes
end Root17
