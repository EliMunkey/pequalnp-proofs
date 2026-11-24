import RSRule12
import RSRule13
import RSRule14
import RSRule15
import RSRule16
import RSRule17
import RSRule18
import RSRule19
import RSRule20
import RSRule21
import RSRule22
import RSRule23
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set1 : Array Rule := #[rule12,rule13,rule14,rule15,rule16,rule17,rule18,rule19,rule20,rule21,rule22,rule23]
theorem each1 (adj : Adj) : ∀ r∈set1.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule12,rule13,rule14,rule15,rule16,rule17,rule18,rule19,rule20,rule21,rule22,rule23] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule12 adj
  · exact okRule13 adj
  · exact okRule14 adj
  · exact okRule15 adj
  · exact okRule16 adj
  · exact okRule17 adj
  · exact okRule18 adj
  · exact okRule19 adj
  · exact okRule20 adj
  · exact okRule21 adj
  · exact okRule22 adj
  · exact okRule23 adj
end Root17
