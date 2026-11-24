import RSPin0
import RSFastWhy
import PetersenRuleBank
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def rule0 : Rule := ⟨0x20000400080000020000400006d9006d9000c400080000100000000000000003000000000000000006000000280030000a000c0000d,0x6d9006d9000c000000000000000000000000003000000000000000006000000280030000a000c0000d,12,0⟩
private def pg0 : List PetersenPackedPin.Instr := []
private theorem prof0 : Profile p0 pg0 rule0.cover rule0.fixed := certify (by decide +kernel)
theorem okRule0 (adj : Adj) : Correct word tgt rule0 := by
  intro fuel L yes; exact fit_sound (valid0 adj) word_injective prof0 yes
end Root17
