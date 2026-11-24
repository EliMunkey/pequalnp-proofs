import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule37 : Rule := ⟨0x1a20008403080000c2000040000400184000800422291101100c00320101882300000300000000000600000c800094000000000200000,0x800420091101000c00300001000200000300000000000600000c000080000000000200000,12,2⟩
private def pg37 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(8,true),(0,true))]
private theorem prof37 : Profile p4 pg37 rule37.cover rule37.fixed := certify (by decide +kernel)
theorem okRule37 (adj : Adj) : Correct word tgt rule37 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof37 yes
end Root17
