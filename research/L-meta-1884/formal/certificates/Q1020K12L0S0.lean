import PetersenLocalChildren
import higher.IndexedNode
import higher.WireProjection
import Q1020K12Data
import Q1020K12L1S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0

private theorem pair0_0_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_8,a0,a1,s1_14]) (hints := [1544,8484,1544,0,773,774,773,3,772,774,1544,1,772,8484,773,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_8,a0,a1,s1_14], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_8) (b1_8 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a0) (via sym4 fix4 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a1) (via sym6 fix6 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_14) (b1_14 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_9,a2,a3,s1_15]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_9,a2,a3,s1_15], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_9) (b1_9 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a2) (via sym4 fix4 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a3) (via sym7 fix7 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_15) (b1_15 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a4,a5,a6,a7]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a4,a5,a6,a7], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a4) (via sym1 fix1 (by decide +kernel) (b1_9 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a5) (via sym2 fix2 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a6) (via sym6 fix6 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a7) (via sym1 fix1 (by decide +kernel) (b1_15 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_10,s1_4,a8,a9]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_10,s1_4,a8,a9], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_10) (b1_10 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_4) (b1_4 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a8) (via sym6 fix6 (by decide +kernel) (b1_4 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a9) (via sym2 fix2 (by decide +kernel) (b1_17 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a10,a11,a12,a13]) (hints := [774,774,10252,0,8453,8484,8453,3,8452,8484,10252,1,8452,774,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a10,a11,a12,a13], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a10) (via sym1 fix1 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a11) (via sym2 fix2 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a12) (via sym7 fix7 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a13) (via sym1 fix1 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_11,a14,a15,a16]) (hints := [774,774,16902,0,18445,24932,18701,3,16902,24932,16902,1,774,774,18701,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_11,a14,a15,a16], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_11) (b1_11 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a14) (via sym1 fix1 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a15) (via sym6 fix6 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a16) (via sym5 fix5 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a17,s1_0,a18,a19]) (hints := [774,774,33800,0,33801,33670,34057,3,33542,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a17,s1_0,a18,a19], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a17) (via sym1 fix1 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_0) (b1_0 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a18) (via sym7 fix7 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a19) (via sym3 fix3 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a20,a21,a22,a23]) (hints := [773,773,33924,0,1542,1544,1542,3,1540,1544,33924,1,1540,773,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a20,a21,a22,a23], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a20) (via sym2 fix2 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a21) (via sym5 fix5 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a22) (via sym7 fix7 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a23) (via sym2 fix2 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a24,a25,a26,s1_16]) (hints := [773,773,10276,0,781,2829,10790,3,2821,2829,10276,1,773,773,10790,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a24,a25,a26,s1_16], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a24) (via sym5 fix5 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a25) (via sym2 fix2 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a26) (via sym4 fix4 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_16) (b1_16 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a27,s1_5,a28,a29]) (hints := [773,773,20548,0,789,4885,37510,3,4869,4885,20548,1,773,773,37510,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a27,s1_5,a28,a29], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a27) (via sym6 fix6 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_5) (b1_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a28) (via sym7 fix7 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a29) (via sym2 fix2 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_12,a30,a31,s1_18]) (hints := [773,773,8453,0,10254,9768,10766,3,8453,9768,8453,1,773,773,10766,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_12,a30,a31,s1_18], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_12) (b1_12 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a30) (via sym2 fix2 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a31) (via sym4 fix4 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_18) (b1_18 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s1_13,a32,a33,s1_19]) (hints := [773,773,18444,0,16902,16964,16902,3,16900,16964,18444,1,16900,773,16902,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s1_13,a32,a33,s1_19], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_13) (b1_13 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a32) (via sym1 fix1 (by decide +kernel) (b1_3 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a33) (via sym4 fix4 (by decide +kernel) (b1_3 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_19) (b1_19 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a34,s1_1,a35,a36]) (hints := [773,773,33800,0,36886,33669,37398,3,33541,33669,33800,1,773,773,37398,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a34,s1_1,a35,a36], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a34) (via sym2 fix2 (by decide +kernel) (b1_12 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_1) (b1_1 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a35) (via sym7 fix7 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a36) (via sym2 fix2 (by decide +kernel) (b1_18 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a37,a38,a39,s1_17]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a37,a38,a39,s1_17], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a37) (via sym2 fix2 (by decide +kernel) (b1_10 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a38) (via sym2 fix2 (by decide +kernel) (b1_4 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a39) (via sym4 fix4 (by decide +kernel) (b1_4 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_17) (b1_17 theta) <|
    PetersenLocalChildren.nil
private theorem pair0_0_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a40,s1_6,a41,a42]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a40,s1_6,a41,a42], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a40) (via sym3 fix3 (by decide +kernel) (b1_9 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_6) (b1_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a41) (via sym5 fix5 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a42) (via sym3 fix3 (by decide +kernel) (b1_15 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a43,a44,a45,a46]) (hints := [8453,1542,8453,0,8457,9766,9481,3,8453,9766,8453,1,9477,1542,9481,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a43,a44,a45,a46], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a43) (via sym3 fix3 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a44) (via sym2 fix2 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a45) (via sym4 fix4 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a46) (via sym1 fix1 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a47,a48,a49,a50]) (hints := [1542,1542,16902,0,18448,50372,19472,3,16902,50372,16902,1,1542,1542,19472,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a47,a48,a49,a50], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a47) (via sym2 fix2 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a48) (via sym3 fix3 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a49) (via sym5 fix5 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a50) (via sym6 fix6 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a51,s1_2,a52,a53]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a51,s1_2,a52,a53], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a51) (via sym3 fix3 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_2) (b1_2 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a52) (via sym4 fix4 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a53) (via sym3 fix3 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a54,a55,a56,a57]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a54,a55,a56,a57], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a54) (via sym5 fix5 (by decide +kernel) (b1_9 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a55) (via sym1 fix1 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a56) (via sym3 fix3 (by decide +kernel) (b1_6 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a57) (via sym5 fix5 (by decide +kernel) (b1_15 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a58,a59,a60,a61]) (hints := [8453,18500,8453,0,10252,10276,10252,3,10244,10276,8453,1,10244,18500,10252,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a58,a59,a60,a61], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a58) (via sym4 fix4 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a59) (via sym6 fix6 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a60) (via sym3 fix3 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a61) (via sym4 fix4 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a62,a63,a64,a65]) (hints := [16902,10276,16902,0,18444,18500,18444,3,18436,18500,16902,1,18436,10276,18444,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a62,a63,a64,a65], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a62) (via sym5 fix5 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a63) (via sym1 fix1 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a64) (via sym2 fix2 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a65) (via sym5 fix5 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a66,a67,a68,a69]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a66,a67,a68,a69], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a66) (via sym4 fix4 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a67) (via sym5 fix5 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a68) (via sym3 fix3 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a69) (via sym7 fix7 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a70,a71,a72,a73]) (hints := [8453,20548,8453,0,8469,28772,12565,3,8453,28772,8453,1,12549,20548,12565,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a70,a71,a72,a73], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a70) (via sym7 fix7 (by decide +kernel) (b1_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a71) (via sym6 fix6 (by decide +kernel) (b1_0 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a72) (via sym1 fix1 (by decide +kernel) (b1_5 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a73) (via sym4 fix4 (by decide +kernel) (b1_16 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a74,a75,s1_7,a76]) (hints := [16902,36996,16902,0,20500,20548,20500,3,20484,20548,16902,1,20484,36996,20500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a74,a75,s1_7,a76], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a74) (via sym6 fix6 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a75) (via sym3 fix3 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_7) (b1_7 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a76) (via sym6 fix6 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a77,a78,a79,a80]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a77,a78,a79,a80], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a77) (via sym7 fix7 (by decide +kernel) (b1_8 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a78) (via sym5 fix5 (by decide +kernel) (b1_2 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a79) (via sym1 fix1 (by decide +kernel) (b1_7 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a80) (via sym7 fix7 (by decide +kernel) (b1_14 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a81,a82,a83,a84]) (hints := [8453,8453,16902,0,16934,24901,25126,3,24837,24901,16902,1,8453,8453,25126,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a81,a82,a83,a84], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a81) (via sym4 fix4 (by decide +kernel) (b1_12 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a82) (via sym1 fix1 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a83) (via sym6 fix6 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a84) (via sym4 fix4 (by decide +kernel) (b1_18 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a85,s1_3,a86,a87]) (hints := [8453,8453,33800,0,40996,41092,40996,3,40964,41092,33800,1,40964,8453,40996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a85,s1_3,a86,a87], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a85) (via sym1 fix1 (by decide +kernel) (b1_13 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := s1_3) (b1_3 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a86) (via sym2 fix2 (by decide +kernel) (b1_3 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a87) (via sym1 fix1 (by decide +kernel) (b1_19 theta)) <|
    PetersenLocalChildren.nil
private theorem pair0_0_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 11 s0_0 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a88,a89,a90,a91]) (hints := [16902,16902,33800,0,33864,49798,50248,3,49670,49798,33800,1,16902,16902,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a88,a89,a90,a91], Blocked tgt 11 V
  exact PetersenLocalChildren.push (P := Blocked tgt 11) (x := a88) (via sym6 fix6 (by decide +kernel) (b1_12 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a89) (via sym5 fix5 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a90) (via sym3 fix3 (by decide +kernel) (b1_1 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 11) (x := a91) (via sym6 fix6 (by decide +kernel) (b1_18 theta)) <|
    PetersenLocalChildren.nil
theorem b0_0 (theta : Extra1020K12.Theta) : Blocked tgt 12 s0_0 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 11 s0_0 pair
  exact PetersenLocalChildren.push (pair0_0_0 theta) <|
    PetersenLocalChildren.push (pair0_0_1 theta) <|
    PetersenLocalChildren.push (pair0_0_2 theta) <|
    PetersenLocalChildren.push (pair0_0_3 theta) <|
    PetersenLocalChildren.push (pair0_0_4 theta) <|
    PetersenLocalChildren.push (pair0_0_5 theta) <|
    PetersenLocalChildren.push (pair0_0_6 theta) <|
    PetersenLocalChildren.push (pair0_0_7 theta) <|
    PetersenLocalChildren.push (pair0_0_8 theta) <|
    PetersenLocalChildren.push (pair0_0_9 theta) <|
    PetersenLocalChildren.push (pair0_0_10 theta) <|
    PetersenLocalChildren.push (pair0_0_11 theta) <|
    PetersenLocalChildren.push (pair0_0_12 theta) <|
    PetersenLocalChildren.push (pair0_0_13 theta) <|
    PetersenLocalChildren.push (pair0_0_14 theta) <|
    PetersenLocalChildren.push (pair0_0_15 theta) <|
    PetersenLocalChildren.push (pair0_0_16 theta) <|
    PetersenLocalChildren.push (pair0_0_17 theta) <|
    PetersenLocalChildren.push (pair0_0_18 theta) <|
    PetersenLocalChildren.push (pair0_0_19 theta) <|
    PetersenLocalChildren.push (pair0_0_20 theta) <|
    PetersenLocalChildren.push (pair0_0_21 theta) <|
    PetersenLocalChildren.push (pair0_0_22 theta) <|
    PetersenLocalChildren.push (pair0_0_23 theta) <|
    PetersenLocalChildren.push (pair0_0_24 theta) <|
    PetersenLocalChildren.push (pair0_0_25 theta) <|
    PetersenLocalChildren.push (pair0_0_26 theta) <|
    PetersenLocalChildren.push (pair0_0_27 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
