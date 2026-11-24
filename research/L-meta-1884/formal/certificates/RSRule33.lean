import RSPin3
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule33 : Rule := ⟨0xa9af200004100800800210004001d40000400000050008400014004001000004000004000c2380000400001000800000020101d00000400,0x8020000000000000001000000004000000000001000040000400400100000400000400040000000400001000000000000000000000000,12,2⟩
private def pg33 : List PetersenPackedPin.Instr := [(false,(0,true),(6,true)),(false,(8,true),(0,true))]
private theorem prof33 : Profile p3 pg33 rule33.cover rule33.fixed := certify (by decide +kernel)
theorem okRule33 (adj : Adj) : Correct word tgt rule33 := by
  intro fuel L yes; exact fit_sound (valid3 adj) word_injective prof33 yes
end Root17
