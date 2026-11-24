import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule18 : Rule := ⟨0x200004200848090201004278040000400000045008044011400900208000900000900090008000c0180080210000000840000000000,0x200848010001004278000000000000005000044001400900208000900000900090008000c0180080210000000840000000000,12,2⟩
private def pg18 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(7,true))]
private theorem prof18 : Profile p1 pg18 rule18.cover rule18.fixed := certify (by decide +kernel)
theorem okRule18 (adj : Adj) : Correct word tgt rule18 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof18 yes
end Root17
