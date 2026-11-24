import RSPin7
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule58 : Rule := ⟨0x201204080800000200004000040004c0000004000800001000000000000000000200800000000000000000000000002000000100000,0x40000004000000000000000000000000000000000000000000000000000000000000000000000,12,2⟩
private def pg58 : List PetersenPackedPin.Instr := [(false,(1,true),(3,true)),(false,(0,true),(8,true))]
private theorem prof58 : Profile p7 pg58 rule58.cover rule58.fixed := certify (by decide +kernel)
theorem okRule58 (adj : Adj) : Correct word tgt rule58 := by
  intro fuel L yes; exact fit_sound (valid7 adj) word_injective prof58 yes
end Root17
