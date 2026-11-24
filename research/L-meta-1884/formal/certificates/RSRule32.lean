import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule32 : Rule := ⟨0x10828a7204304100800800210004001cc00004000000d000840003400400100000400000400262380000400001000000002002100d00080000,0x8020010000000000001000000004000000000001000040000400400100000400000400040000000400001000000002000000000000000,12,2⟩
private def pg32 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(0,false),(8,true))]
private theorem prof32 : Profile p3 pg32 rule32.cover rule32.fixed := certify (by decide +kernel)
theorem okRule32 (adj : Adj) : Correct word tgt rule32 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof32 yes
end Root17
