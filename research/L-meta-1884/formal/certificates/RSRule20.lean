import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule20 : Rule := ⟨0x8000200004200a48000201005268040000400045045008044011400900208000901400900090008000c000008021000000084000000a000,0x200a48000001005268000000000005005000044001400900208000901400900090008000c000008021000000084000000a000,12,2⟩
private def pg20 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(5,true),(4,true))]
private theorem prof20 : Profile p1 pg20 rule20.cover rule20.fixed := certify (by decide +kernel)
theorem okRule20 (adj : Adj) : Correct word tgt rule20 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof20 yes
end Root17
