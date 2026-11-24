import RSRule0
import RSRule1
import RSRule2
import RSRule3
import RSRule4
import RSRule5
import RSRule6
import RSRule7
import RSRule8
import RSRule9
import RSRule10
import RSRule11
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set0 : Array Rule := #[rule0,rule1,rule2,rule3,rule4,rule5,rule6,rule7,rule8,rule9,rule10,rule11]
theorem each0 (adj : Adj) : ∀ r∈set0.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule0,rule1,rule2,rule3,rule4,rule5,rule6,rule7,rule8,rule9,rule10,rule11] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule0 adj
  · exact okRule1 adj
  · exact okRule2 adj
  · exact okRule3 adj
  · exact okRule4 adj
  · exact okRule5 adj
  · exact okRule6 adj
  · exact okRule7 adj
  · exact okRule8 adj
  · exact okRule9 adj
  · exact okRule10 adj
  · exact okRule11 adj
end Root17
