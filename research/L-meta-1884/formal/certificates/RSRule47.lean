import RSPin5
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule47 : Rule := ⟨0x8000020000400080000030000400004000040000004000800001080020000000000000020000000000000000100000000000000000000020,0x30000000000000000000000000800000080020000000000000020000000000000000100000000000000000000020,12,3⟩
private def pg47 : List PetersenPackedPin.Instr := [(false,(0,true),(4,true)),(false,(0,false),(4,true)),(false,(0,false),(4,true))]
private theorem prof47 : Profile p5 pg47 rule47.cover rule47.fixed := certify (by decide +kernel)
theorem okRule47 (adj : Adj) : Correct word tgt rule47 := by
  intro fuel L yes; exact fit_sound (valid5 adj) word_injective prof47 yes
end Root17
