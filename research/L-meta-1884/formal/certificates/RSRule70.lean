import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule70 : Rule := ⟨0x20000490c80008020000400004000040000004000000001000000010000000000000000000000000000203000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg70 : List PetersenPackedPin.Instr := [(false,(1,true),(5,true)),(false,(1,true),(0,true))]
private theorem prof70 : Profile p9 pg70 rule70.cover rule70.fixed := certify (by decide +kernel)
theorem okRule70 (adj : Adj) : Correct word tgt rule70 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof70 yes
end Root17
