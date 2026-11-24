import RSRule84
import RSRule85
import RSRule86
import RSRule87
import RSRule88
import RSRule89
import RSRule90
import RSRule91
import RSRule92
import RSRule93
import RSRule94
import RSRule95
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set7 : Array Rule := #[rule84,rule85,rule86,rule87,rule88,rule89,rule90,rule91,rule92,rule93,rule94,rule95]
theorem each7 (adj : Adj) : ∀ r∈set7.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule84,rule85,rule86,rule87,rule88,rule89,rule90,rule91,rule92,rule93,rule94,rule95] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule84 adj
  · exact okRule85 adj
  · exact okRule86 adj
  · exact okRule87 adj
  · exact okRule88 adj
  · exact okRule89 adj
  · exact okRule90 adj
  · exact okRule91 adj
  · exact okRule92 adj
  · exact okRule93 adj
  · exact okRule94 adj
  · exact okRule95 adj
end Root17
