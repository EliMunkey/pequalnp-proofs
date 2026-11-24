import RSRule96
import RSRule97
import RSRule98
import RSRule99
import RSRule100
import RSRule101
import RSRule102
import RSRule103
import RSRule104
import RSRule105
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set8 : Array Rule := #[rule96,rule97,rule98,rule99,rule100,rule101,rule102,rule103,rule104,rule105]
theorem each8 (adj : Adj) : ∀ r∈set8.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule96,rule97,rule98,rule99,rule100,rule101,rule102,rule103,rule104,rule105] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule96 adj
  · exact okRule97 adj
  · exact okRule98 adj
  · exact okRule99 adj
  · exact okRule100 adj
  · exact okRule101 adj
  · exact okRule102 adj
  · exact okRule103 adj
  · exact okRule104 adj
  · exact okRule105 adj
end Root17
