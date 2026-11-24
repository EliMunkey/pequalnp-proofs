import RSRule48
import RSRule49
import RSRule50
import RSRule51
import RSRule52
import RSRule53
import RSRule54
import RSRule55
import RSRule56
import RSRule57
import RSRule58
import RSRule59
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set4 : Array Rule := #[rule48,rule49,rule50,rule51,rule52,rule53,rule54,rule55,rule56,rule57,rule58,rule59]
theorem each4 (adj : Adj) : ∀ r∈set4.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule48,rule49,rule50,rule51,rule52,rule53,rule54,rule55,rule56,rule57,rule58,rule59] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule48 adj
  · exact okRule49 adj
  · exact okRule50 adj
  · exact okRule51 adj
  · exact okRule52 adj
  · exact okRule53 adj
  · exact okRule54 adj
  · exact okRule55 adj
  · exact okRule56 adj
  · exact okRule57 adj
  · exact okRule58 adj
  · exact okRule59 adj
end Root17
