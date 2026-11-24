import RSPin9
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule72 : Rule := ⟨0x4008000020000400880000020000400004000040000004000800001000000000000000000000000000000000008002000000000000000000000,0x80000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg72 : List PetersenPackedPin.Instr := [(false,(1,true),(7,true)),(false,(0,false),(4,true))]
private theorem prof72 : Profile p9 pg72 rule72.cover rule72.fixed := certify (by decide +kernel)
theorem okRule72 (adj : Adj) : Correct word tgt rule72 := by
  intro fuel L yes; exact fit_sound (valid9 adj) word_injective prof72 yes
end Root17
