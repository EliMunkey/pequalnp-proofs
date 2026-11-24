import RSRule72
import RSRule73
import RSRule74
import RSRule75
import RSRule76
import RSRule77
import RSRule78
import RSRule79
import RSRule80
import RSRule81
import RSRule82
import RSRule83
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set6 : Array Rule := #[rule72,rule73,rule74,rule75,rule76,rule77,rule78,rule79,rule80,rule81,rule82,rule83]
theorem each6 (adj : Adj) : ∀ r∈set6.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule72,rule73,rule74,rule75,rule76,rule77,rule78,rule79,rule80,rule81,rule82,rule83] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule72 adj
  · exact okRule73 adj
  · exact okRule74 adj
  · exact okRule75 adj
  · exact okRule76 adj
  · exact okRule77 adj
  · exact okRule78 adj
  · exact okRule79 adj
  · exact okRule80 adj
  · exact okRule81 adj
  · exact okRule82 adj
  · exact okRule83 adj
end Root17
