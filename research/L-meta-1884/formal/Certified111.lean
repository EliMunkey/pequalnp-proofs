import PetersenTightCost

open PetersenWordCost PetersenSignalCut PetersenShortPrefix PetersenPrefixCost PetersenTightPrefix
namespace PetersenGraphCosts.M111

private def input : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
private def tgt : BitVec 64 := 0xfeeefcccfaeaf8c8
private def neg : List (Fin 64) := [26, 5, 41, 52, 56, 2]
private def probes : Pairs 64 := [(2, 3), (1, 3), (2, 6), (4, 12), (1, 17), (2, 34)]

private def branch (a b : BitVec 64) : Bool := a == b || (choices a b).all fun o =>
  input.contains o || [false,true].all fun da => [false,true].all fun db =>
    tightExclude choices tgt neg 3 5 (successor input a b o da db)

set_option maxRecDepth 200000
set_option maxHeartbeats 0
private theorem pair_0_0 : branch 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_0_1 : branch 0xaaaaaaaaaaaaaaaa 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_0_2 : branch 0xaaaaaaaaaaaaaaaa 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_0_3 : branch 0xaaaaaaaaaaaaaaaa 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_0_4 : branch 0xaaaaaaaaaaaaaaaa 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_0_5 : branch 0xaaaaaaaaaaaaaaaa 0xffffffff00000000 = true := by decide +kernel
private theorem pair_1_0 : branch 0xcccccccccccccccc 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_1_1 : branch 0xcccccccccccccccc 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_1_2 : branch 0xcccccccccccccccc 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_1_3 : branch 0xcccccccccccccccc 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_1_4 : branch 0xcccccccccccccccc 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_1_5 : branch 0xcccccccccccccccc 0xffffffff00000000 = true := by decide +kernel
private theorem pair_2_0 : branch 0xf0f0f0f0f0f0f0f0 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_2_1 : branch 0xf0f0f0f0f0f0f0f0 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_2_2 : branch 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_2_3 : branch 0xf0f0f0f0f0f0f0f0 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_2_4 : branch 0xf0f0f0f0f0f0f0f0 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_2_5 : branch 0xf0f0f0f0f0f0f0f0 0xffffffff00000000 = true := by decide +kernel
private theorem pair_3_0 : branch 0xff00ff00ff00ff00 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_3_1 : branch 0xff00ff00ff00ff00 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_3_2 : branch 0xff00ff00ff00ff00 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_3_3 : branch 0xff00ff00ff00ff00 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_3_4 : branch 0xff00ff00ff00ff00 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_3_5 : branch 0xff00ff00ff00ff00 0xffffffff00000000 = true := by decide +kernel
private theorem pair_4_0 : branch 0xffff0000ffff0000 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_4_1 : branch 0xffff0000ffff0000 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_4_2 : branch 0xffff0000ffff0000 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_4_3 : branch 0xffff0000ffff0000 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_4_4 : branch 0xffff0000ffff0000 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_4_5 : branch 0xffff0000ffff0000 0xffffffff00000000 = true := by decide +kernel
private theorem pair_5_0 : branch 0xffffffff00000000 0xaaaaaaaaaaaaaaaa = true := by decide +kernel
private theorem pair_5_1 : branch 0xffffffff00000000 0xcccccccccccccccc = true := by decide +kernel
private theorem pair_5_2 : branch 0xffffffff00000000 0xf0f0f0f0f0f0f0f0 = true := by decide +kernel
private theorem pair_5_3 : branch 0xffffffff00000000 0xff00ff00ff00ff00 = true := by decide +kernel
private theorem pair_5_4 : branch 0xffffffff00000000 0xffff0000ffff0000 = true := by decide +kernel
private theorem pair_5_5 : branch 0xffffffff00000000 0xffffffff00000000 = true := by decide +kernel

private theorem closed : tightExclude choices tgt neg 4 6 input = true := by
  change (if !viable input tgt neg 6 then true else if input.contains tgt then false else
    input.all fun a => input.all fun b => branch a b) = true
  rw [show viable input tgt neg 6 = true by decide, show input.contains tgt = false by decide]
  simp only [Bool.not_true, Bool.false_eq_true, if_false, input, List.all_cons, List.all_nil,
    Bool.and_true,pair_0_0,pair_0_1,pair_0_2,pair_0_3,pair_0_4,pair_0_5,pair_1_0,pair_1_1,pair_1_2,pair_1_3,pair_1_4,pair_1_5,pair_2_0,pair_2_1,pair_2_2,pair_2_3,pair_2_4,pair_2_5,pair_3_0,pair_3_1,pair_3_2,pair_3_3,pair_3_4,pair_3_5,pair_4_0,pair_4_1,pair_4_2,pair_4_3,pair_4_4,pair_4_5,pair_5_0,pair_5_1,pair_5_2,pair_5_3,pair_5_4,pair_5_5]

theorem bound : NoAtMost (inputs 6) (graphTarget 6 [(0, 1), (1, 2), (2, 3), (0, 4), (1, 5)]) 6 := by
  change NoAtMost input tgt 6
  exact PetersenTightCost.certified (by decide) input tgt probes neg 4 6 (by decide) (by decide) 3 (by decide) (by decide) closed

#print axioms bound
end PetersenGraphCosts.M111
