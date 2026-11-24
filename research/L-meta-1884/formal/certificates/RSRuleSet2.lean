import RSRule24
import RSRule25
import RSRule26
import RSRule27
import RSRule28
import RSRule29
import RSRule30
import RSRule31
import RSRule32
import RSRule33
import RSRule34
import RSRule35
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set2 : Array Rule := #[rule24,rule25,rule26,rule27,rule28,rule29,rule30,rule31,rule32,rule33,rule34,rule35]
theorem each2 (adj : Adj) : ∀ r∈set2.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule24,rule25,rule26,rule27,rule28,rule29,rule30,rule31,rule32,rule33,rule34,rule35] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule24 adj
  · exact okRule25 adj
  · exact okRule26 adj
  · exact okRule27 adj
  · exact okRule28 adj
  · exact okRule29 adj
  · exact okRule30 adj
  · exact okRule31 adj
  · exact okRule32 adj
  · exact okRule33 adj
  · exact okRule34 adj
  · exact okRule35 adj
end Root17
