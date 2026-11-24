import RSRule36
import RSRule37
import RSRule38
import RSRule39
import RSRule40
import RSRule41
import RSRule42
import RSRule43
import RSRule44
import RSRule45
import RSRule46
import RSRule47
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set3 : Array Rule := #[rule36,rule37,rule38,rule39,rule40,rule41,rule42,rule43,rule44,rule45,rule46,rule47]
theorem each3 (adj : Adj) : ∀ r∈set3.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule36,rule37,rule38,rule39,rule40,rule41,rule42,rule43,rule44,rule45,rule46,rule47] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule36 adj
  · exact okRule37 adj
  · exact okRule38 adj
  · exact okRule39 adj
  · exact okRule40 adj
  · exact okRule41 adj
  · exact okRule42 adj
  · exact okRule43 adj
  · exact okRule44 adj
  · exact okRule45 adj
  · exact okRule46 adj
  · exact okRule47 adj
end Root17
