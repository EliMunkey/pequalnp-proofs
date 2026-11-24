import RSPin1
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule19 : Rule := ⟨0x200004200848090201004278040000400000045040008011400900124000900000900090008000c0180080210000000840000000000,0x200848010001004278000000000000005040008001400900024000900000900090008000c0180080210000000840000000000,12,3⟩
private def pg19 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(7,true)),(false,(3,true),(0,true))]
private theorem prof19 : Profile p1 pg19 rule19.cover rule19.fixed := certify (by decide +kernel)
theorem okRule19 (adj : Adj) : Correct word tgt rule19 := by
  intro fuel L yes; exact fit_sound (valid1 adj) word_injective prof19 yes
end Root17
