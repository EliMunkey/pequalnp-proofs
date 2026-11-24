import RSRule60
import RSRule61
import RSRule62
import RSRule63
import RSRule64
import RSRule65
import RSRule66
import RSRule67
import RSRule68
import RSRule69
import RSRule70
import RSRule71
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def set5 : Array Rule := #[rule60,rule61,rule62,rule63,rule64,rule65,rule66,rule67,rule68,rule69,rule70,rule71]
theorem each5 (adj : Adj) : ∀ r∈set5.toList, Correct word tgt r := by
  intro r mem
  change r∈[rule60,rule61,rule62,rule63,rule64,rule65,rule66,rule67,rule68,rule69,rule70,rule71] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact okRule60 adj
  · exact okRule61 adj
  · exact okRule62 adj
  · exact okRule63 adj
  · exact okRule64 adj
  · exact okRule65 adj
  · exact okRule66 adj
  · exact okRule67 adj
  · exact okRule68 adj
  · exact okRule69 adj
  · exact okRule70 adj
  · exact okRule71 adj
end Root17
