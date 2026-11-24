import PetersenTightCost

open PetersenWordCost PetersenSignalCut PetersenShortPrefix PetersenPrefixCost
open PetersenTightPrefix
namespace PetersenCycleFive

def input : List (BitVec 32) := [0xAAAAAAAA,0xCCCCCCCC,0xF0F0F0F0,0xFF00FF00,0xFFFF0000]
def target : BitVec 32 := 0xFFEAF8C8
def neg : List (Fin 32) := [5,9,10,18,20]

/-- Any of these pairs suffices to force its corresponding primary to be in the used-input set. -/
def probes : Pairs 32 := [(2,3),(1,3),(2,6),(4,12),(8,24)]

theorem exact_table : ∀ r : Fin 32, PetersenWordCost.read target r =
    ((r.val.testBit 0 && r.val.testBit 1) || (r.val.testBit 1 && r.val.testBit 2) ||
     (r.val.testBit 2 && r.val.testBit 3) || (r.val.testBit 3 && r.val.testBit 4) ||
     (r.val.testBit 4 && r.val.testBit 0)) := by decide

theorem every_input_forced : forcedSet input target probes = input.toFinset := by decide



def branch (a b : BitVec 32) : Bool := a == b || (choices a b).all fun o =>
  input.contains o || [false,true].all fun da => [false,true].all fun db =>
    tightExclude choices target neg 2 5 (successor input a b o da db)

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private theorem branch_0_0 : branch 0xAAAAAAAA 0xAAAAAAAA = true := by decide +kernel
private theorem branch_0_1 : branch 0xAAAAAAAA 0xCCCCCCCC = true := by decide +kernel
private theorem branch_0_2 : branch 0xAAAAAAAA 0xF0F0F0F0 = true := by decide +kernel
private theorem branch_0_3 : branch 0xAAAAAAAA 0xFF00FF00 = true := by decide +kernel
private theorem branch_0_4 : branch 0xAAAAAAAA 0xFFFF0000 = true := by decide +kernel
private theorem branch_1_0 : branch 0xCCCCCCCC 0xAAAAAAAA = true := by decide +kernel
private theorem branch_1_1 : branch 0xCCCCCCCC 0xCCCCCCCC = true := by decide +kernel
private theorem branch_1_2 : branch 0xCCCCCCCC 0xF0F0F0F0 = true := by decide +kernel
private theorem branch_1_3 : branch 0xCCCCCCCC 0xFF00FF00 = true := by decide +kernel
private theorem branch_1_4 : branch 0xCCCCCCCC 0xFFFF0000 = true := by decide +kernel
private theorem branch_2_0 : branch 0xF0F0F0F0 0xAAAAAAAA = true := by decide +kernel
private theorem branch_2_1 : branch 0xF0F0F0F0 0xCCCCCCCC = true := by decide +kernel
private theorem branch_2_2 : branch 0xF0F0F0F0 0xF0F0F0F0 = true := by decide +kernel
private theorem branch_2_3 : branch 0xF0F0F0F0 0xFF00FF00 = true := by decide +kernel
private theorem branch_2_4 : branch 0xF0F0F0F0 0xFFFF0000 = true := by decide +kernel
private theorem branch_3_0 : branch 0xFF00FF00 0xAAAAAAAA = true := by decide +kernel
private theorem branch_3_1 : branch 0xFF00FF00 0xCCCCCCCC = true := by decide +kernel
private theorem branch_3_2 : branch 0xFF00FF00 0xF0F0F0F0 = true := by decide +kernel
private theorem branch_3_3 : branch 0xFF00FF00 0xFF00FF00 = true := by decide +kernel
private theorem branch_3_4 : branch 0xFF00FF00 0xFFFF0000 = true := by decide +kernel
private theorem branch_4_0 : branch 0xFFFF0000 0xAAAAAAAA = true := by decide +kernel
private theorem branch_4_1 : branch 0xFFFF0000 0xCCCCCCCC = true := by decide +kernel
private theorem branch_4_2 : branch 0xFFFF0000 0xF0F0F0F0 = true := by decide +kernel
private theorem branch_4_3 : branch 0xFFFF0000 0xFF00FF00 = true := by decide +kernel
private theorem branch_4_4 : branch 0xFFFF0000 0xFFFF0000 = true := by decide +kernel

theorem exhaustive : tightExclude choices target neg 3 6 input = true := by
  change (if !viable input target neg 6 then true else if input.contains target then false else
    input.all fun a => input.all fun b => branch a b) = true
  rw [show viable input target neg 6 = true by decide, show input.contains target = false by decide]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, input, List.all_cons, List.all_nil, Bool.and_true,branch_0_0,branch_0_1,branch_0_2,branch_0_3,branch_0_4,branch_1_0,branch_1_1,branch_1_2,branch_1_3,branch_1_4,branch_2_0,branch_2_1,branch_2_2,branch_2_3,branch_2_4,branch_3_0,branch_3_1,branch_3_2,branch_3_3,branch_3_4,branch_4_0,branch_4_1,branch_4_2,branch_4_3,branch_4_4]

theorem no_six_gates : NoAtMost input target 6 :=
  PetersenTightCost.certified (by decide) input target probes neg 3 6 (by decide) (by decide) 3
    (by decide) every_input_forced exhaustive

#print axioms no_six_gates
end PetersenCycleFive
