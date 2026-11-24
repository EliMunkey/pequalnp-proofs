import RSWhichRule
import RSRuleSet0
import RSRuleSet1
import RSRuleSet2
import RSRuleSet3
import RSRuleSet4
import RSRuleSet5
import RSRuleSet6
import RSRuleSet7
import RSRuleSet8
namespace Root17
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048
open PetersenBitBank PetersenRuleBank
def ruleSet := #[set0,set1,set2,set3,set4,set5,set6,set7,set8]
def rules (i : Nat) : Rule := get ((ruleSet[i/12]?).getD #[]) (i%12) rule0
theorem validRules (adj : Adj) : ∀ i, Correct word tgt (rules i) := by
  intro i; apply entries (okRule0 adj); intro r h
  cases hh : ruleSet[i/12]? with
  | none => simp [hh] at h
  | some a =>
    have hm : a ∈ ruleSet.toList := by simpa using Array.mem_of_getElem? hh
    simp only [hh,Option.getD_some] at h
    change a∈[set0,set1,set2,set3,set4,set5,set6,set7,set8] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · intro fuel L test; exact each0 adj r h test
    · intro fuel L test; exact each1 adj r h test
    · intro fuel L test; exact each2 adj r h test
    · intro fuel L test; exact each3 adj r h test
    · intro fuel L test; exact each4 adj r h test
    · intro fuel L test; exact each5 adj r h test
    · intro fuel L test; exact each6 adj r h test
    · intro fuel L test; exact each7 adj r h test
    · intro fuel L test; exact each8 adj r h test
end Root17
