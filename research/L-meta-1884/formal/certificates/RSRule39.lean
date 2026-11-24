import RSPin4
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule39 : Rule := ⟨0x18000020000403080000c20000400004001840008004220c0101100c00380101a02300000300000000000600000c000000000000000000002,0x8004200c0101000c00300001000200000300000000000600000c000000000000000000002,12,2⟩
private def pg39 : List PetersenPackedPin.Instr := [(false,(0,true),(7,true)),(false,(0,false),(7,true))]
private theorem prof39 : Profile p4 pg39 rule39.cover rule39.fixed := certify (by decide +kernel)
theorem okRule39 (adj : Adj) : Correct word tgt rule39 := by
  intro fuel L yes; exact fit_sound (valid4 adj) word_injective prof39 yes
end Root17
