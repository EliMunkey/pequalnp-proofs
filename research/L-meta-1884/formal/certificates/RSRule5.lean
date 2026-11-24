import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule5 : Rule := ⟨0x820000400080000020000400404aec04aee00040c080014103000c00028000c000008000800180030000060007800000014000c00001,0x404aec04aee00000c000014003000c00028000c000008000800180030000060007800000014000c00001,12,2⟩
private def pg5 : List PetersenPackedPin.Instr := [(false,(0,true),(2,true)),(false,(0,false),(5,true))]
private theorem prof5 : Profile p0 pg5 rule5.cover rule5.fixed := certify (by decide +kernel)
theorem okRule5 (adj : Adj) : Correct word tgt rule5 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof5 yes
end Root17
