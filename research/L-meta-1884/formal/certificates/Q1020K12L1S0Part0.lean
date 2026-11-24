import PetersenLocalChildren
import Q1020K12L1S0Local
import Q1020K12L2S0
import Q1020K12L2S1
import Q1020K12L2S2
import Q1020K12L2S3
import Q1020K12L2S4
import Q1020K12L2S9
import Q1020K12L2S10
import Q1020K12L2S11
import Q1020K12L2S12
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L1S0Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
theorem b1_0 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_0 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s1_0 11 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
private theorem pair1_1_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_35,s2_34,a92,a93,a94,s2_132,s2_429,s2_133]) (hints := [8488,0,8488,1,778,6,778,7,8488,2,8488,3,778,4,778,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_35,s2_34,a92,a93,a94,s2_132,s2_429,s2_133], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_35) (b2_35 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_34) (b2_34 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a92) (via sym5 fix5 (by decide +kernel) (b2_33 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a93) (via sym5 fix5 (by decide +kernel) (b2_32 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a94) (via sym1 fix1 (by decide +kernel) (b2_421 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_132) (b2_132 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_429) (b2_429 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_133) (b2_133 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_0,a95,s2_140,s2_139]) (hints := [774,0,33670,1,774,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_0,a95,s2_140,s2_139], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_0) (b2_0 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a95) (via sym2 fix2 (by decide +kernel) (b2_460 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_140) (b2_140 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_139) (b2_139 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_65,s2_64,a96,a97,a98,s2_147,a99,s2_148]) (hints := [33928,0,33928,1,1546,6,1546,7,33928,2,33928,3,1546,4,1546,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_65,s2_64,a96,a97,a98,s2_147,a99,s2_148], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_65) (b2_65 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_64) (b2_64 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a96) (via sym5 fix5 (by decide +kernel) (b2_27 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a97) (via sym5 fix5 (by decide +kernel) (b2_26 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a98) (via sym3 fix3 (by decide +kernel) (b2_387 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_147) (b2_147 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a99) (via sym2 fix2 (by decide +kernel) (b2_432 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_148) (b2_148 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a100,a101,s2_29,s2_28,a102,s2_155,a103,s2_156]) (hints := [10280,0,10280,1,10794,6,10794,7,10280,2,10280,3,10794,4,10794,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a100,a101,s2_29,s2_28,a102,s2_155,a103,s2_156], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a100) (via sym5 fix5 (by decide +kernel) (b2_39 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a101) (via sym5 fix5 (by decide +kernel) (b2_38 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_29) (b2_29 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_28) (b2_28 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a102) (via sym4 fix4 (by decide +kernel) (b2_420 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_155) (b2_155 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a103) (via sym5 fix5 (by decide +kernel) (b2_431 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_156) (b2_156 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_67,s2_66,s2_23,s2_22,a104,a105,s2_164,s2_163,s2_538,a106,s2_197,s2_165]) (hints := [20556,0,20556,1,8,9,10,11,20556,2,20556,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_67,s2_66,s2_23,s2_22,a104,a105,s2_164,s2_163,s2_538,a106,s2_197,s2_165], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_67) (b2_67 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_66) (b2_66 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_23) (b2_23 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_22) (b2_22 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a104) (via sym7 fix7 (by decide +kernel) (b2_385 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a105) (via sym7 fix7 (by decide +kernel) (b2_384 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_164) (b2_164 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_163) (b2_163 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_538) (b2_538 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a106) (via sym6 fix6 (by decide +kernel) (b2_433 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_197) (b2_197 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_165) (b2_165 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_71,s2_68,s2_20,s2_19,a107,s2_172,a108,s2_173]) (hints := [8457,0,8457,1,10770,6,10770,7,8457,2,8457,3,10770,4,10770,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_71,s2_68,s2_20,s2_19,a107,s2_172,a108,s2_173], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_71) (b2_71 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_68) (b2_68 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_20) (b2_20 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_19) (b2_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a107) (via sym4 fix4 (by decide +kernel) (b2_483 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_172) (b2_172 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a108) (via sym1 fix1 (by decide +kernel) (b2_490 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_173) (b2_173 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_74,s2_72,s2_11,s2_9,a109,s2_180,a110,s2_181]) (hints := [18448,0,18448,1,16906,6,16906,7,18448,2,18448,3,16906,4,16906,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_74,s2_72,s2_11,s2_9,a109,s2_180,a110,s2_181], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_74) (b2_74 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_72) (b2_72 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_11) (b2_11 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_9) (b2_9 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a109) (via sym7 fix7 (by decide +kernel) (b2_465 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_180) (b2_180 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a110) (via sym5 fix5 (by decide +kernel) (b2_489 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_181) (b2_181 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_0,a111,s2_196,s2_190]) (hints := [33801,0,33801,1,37399,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_0,a111,s2_196,s2_190], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_0) (b2_0 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a111) (via sym2 fix2 (by decide +kernel) (b2_522 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_196) (b2_196 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_190) (b2_190 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_125,s2_113,s2_118,s2_141]) (hints := [8484,8484,49860,0,774,774,33669,3,774,774,49860,1,8484,8484,33669,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_125,s2_113,s2_118,s2_141], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_125) (b2_125 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_113) (b2_113 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_118) (b2_118 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_141) (b2_141 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_126,s2_105,s2_119,s2_149]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_126,s2_105,s2_119,s2_149], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_126) (b2_126 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_105) (b2_105 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_119) (b2_119 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_149) (b2_149 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_127,s2_98,s2_120,s2_157]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_127,s2_98,s2_120,s2_157], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_127) (b2_127 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_98) (b2_98 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_120) (b2_120 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_157) (b2_157 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_128,s2_90,s2_121,s2_166]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_128,s2_90,s2_121,s2_166], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_128) (b2_128 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_90) (b2_90 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_121) (b2_121 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_166) (b2_166 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_129,s2_84,s2_122,s2_174]) (hints := [774,774,10252,0,8453,8484,8453,3,8452,8484,10252,1,8452,774,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_129,s2_84,s2_122,s2_174], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_129) (b2_129 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_84) (b2_84 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_122) (b2_122 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_174) (b2_174 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_130,a112,s2_123,s2_182]) (hints := [774,774,16902,0,18445,24932,18701,3,16902,24932,16902,1,774,774,18701,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_130,a112,s2_123,s2_182], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_130) (b2_130 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a112) (via sym1 fix1 (by decide +kernel) (b2_44 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_123) (b2_123 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_182) (b2_182 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_131,s2_40,s2_124,s2_189]) (hints := [774,774,33800,0,33801,33670,34057,3,33800,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_131,s2_40,s2_124,s2_189], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_131) (b2_131 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_40) (b2_40 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_124) (b2_124 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_189) (b2_189 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_134,s2_107,s2_106,s2_114,s2_198,s2_150]) (hints := [33926,33671,33926,0,1544,4,1544,5,33926,1,33926,2,1544,33671,1544,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_134,s2_107,s2_106,s2_114,s2_198,s2_150], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_134) (b2_134 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_107) (b2_107 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_106) (b2_106 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_114) (b2_114 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_198) (b2_198 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_150) (b2_150 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_135,s2_99,a113,s2_158]) (hints := [10276,33669,10276,0,10790,35725,10790,3,10276,35725,10276,1,10790,33669,10790,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_135,s2_99,a113,s2_158], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_135) (b2_135 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_99) (b2_99 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a113) (via sym4 fix4 (by decide +kernel) (b2_45 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_158) (b2_158 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_136,s2_92,s2_91,a114,s2_199,s2_167]) (hints := [20550,33671,20550,0,37000,4,37512,5,20550,1,20550,2,37510,33671,37512,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_136,s2_92,s2_91,a114,s2_199,s2_167], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_136) (b2_136 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_92) (b2_92 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_91) (b2_91 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a114) (via sym7 fix7 (by decide +kernel) (b2_51 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_199) (b2_199 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_167) (b2_167 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_137,s2_86,s2_85,a115,s2_200,s2_175]) (hints := [8455,33671,8455,0,10768,4,10768,5,8455,1,8455,2,10768,33671,10768,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_137,s2_86,s2_85,a115,s2_200,s2_175], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_137) (b2_137 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_86) (b2_86 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_85) (b2_85 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a115) (via sym4 fix4 (by decide +kernel) (b2_83 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_200) (b2_200 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_175) (b2_175 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_138,s2_79,s2_115,s2_183]) (hints := [18444,33669,18444,0,16902,49860,16902,3,18444,49860,18444,1,16902,33669,16902,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_138,s2_79,s2_115,s2_183], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_138) (b2_138 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_79) (b2_79 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_115) (b2_115 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_183) (b2_183 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_140,s2_139,s2_196,s2_190,a116,s2_116,s2_117]) (hints := [33803,0,33803,1,33672,33672,2,3,33544,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_140,s2_139,s2_196,s2_190,a116,s2_116,s2_117], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_140) (b2_140 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_139) (b2_139 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_196) (b2_196 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_190) (b2_190 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a116) (via sym7 fix7 (by decide +kernel) (b2_116 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_116) (b2_116 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_117) (b2_117 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_142,s2_100,s2_108,s2_159]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_142,s2_100,s2_108,s2_159], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_142) (b2_142 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_100) (b2_100 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_108) (b2_108 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_159) (b2_159 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_143,s2_93,s2_109,s2_168]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_143,s2_93,s2_109,s2_168], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_143) (b2_143 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_93) (b2_93 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_109) (b2_109 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_168) (b2_168 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_144,a117,s2_110,s2_176]) (hints := [8453,1542,8453,0,8457,9766,9481,3,8453,9766,8453,1,9477,1542,9481,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_144,a117,s2_110,s2_176], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_144) (b2_144 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a117) (via sym2 fix2 (by decide +kernel) (b2_46 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_110) (b2_110 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_176) (b2_176 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_145,a118,s2_111,s2_184]) (hints := [1542,1542,16902,0,18448,50372,19472,3,16902,50372,16902,1,1542,1542,19472,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_145,a118,s2_111,s2_184], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_145) (b2_145 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a118) (via sym3 fix3 (by decide +kernel) (b2_49 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_111) (b2_111 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_184) (b2_184 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_146,s2_75,s2_112,s2_191]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_146,s2_75,s2_112,s2_191], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_146) (b2_146 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_75) (b2_75 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_112) (b2_112 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_191) (b2_191 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_151,s2_94,s2_101,s2_169]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_151,s2_94,s2_101,s2_169], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_151) (b2_151 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_94) (b2_94 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_101) (b2_101 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_169) (b2_169 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_152,s2_87,s2_102,s2_177]) (hints := [8453,18500,8453,0,10252,10276,10252,3,10244,10276,8453,1,10244,18500,10252,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_152,s2_87,s2_102,s2_177], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_152) (b2_152 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_87) (b2_87 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_102) (b2_102 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_177) (b2_177 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_153,s2_80,s2_103,s2_185]) (hints := [16902,10276,16902,0,18444,18500,18444,3,18436,18500,16902,1,18436,10276,18444,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_153,s2_80,s2_103,s2_185], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_153) (b2_153 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_80) (b2_80 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_103) (b2_103 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_185) (b2_185 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_154,a119,s2_104,s2_192]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_154,a119,s2_104,s2_192], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_154) (b2_154 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a119) (via sym5 fix5 (by decide +kernel) (b2_42 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_104) (b2_104 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_192) (b2_192 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_160,a120,s2_95,s2_178]) (hints := [8453,20548,8453,0,8469,28772,12565,3,8453,28772,8453,1,12549,20548,12565,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_160,a120,s2_95,s2_178], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_160) (b2_160 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a120) (via sym6 fix6 (by decide +kernel) (b2_47 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_95) (b2_95 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_178) (b2_178 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_161,s2_81,s2_96,s2_186]) (hints := [16902,36996,16902,0,20500,20548,20500,3,20484,20548,16902,1,20484,36996,20500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_161,s2_81,s2_96,s2_186], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_161) (b2_161 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_81) (b2_81 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_96) (b2_96 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_186) (b2_186 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_162,s2_76,s2_97,s2_193]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_162,s2_76,s2_97,s2_193], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_162) (b2_162 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_76) (b2_76 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_97) (b2_97 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_193) (b2_193 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_170,s2_82,s2_88,s2_187]) (hints := [8453,8453,16902,0,16934,24901,25126,3,24837,24901,16902,1,8453,8453,25126,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_170,s2_82,s2_88,s2_187], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_170) (b2_170 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_82) (b2_82 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_88) (b2_88 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_187) (b2_187 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_171,s2_77,s2_89,s2_194]) (hints := [8453,8453,33800,0,40996,41092,40996,3,40964,41092,33800,1,40964,8453,40996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_171,s2_77,s2_89,s2_194], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_171) (b2_171 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_77) (b2_77 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_89) (b2_89 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_194) (b2_194 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_1_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_1 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_179,s2_78,s2_83,s2_195]) (hints := [16902,16902,33800,0,33864,49798,50248,3,33800,49798,33800,1,16902,16902,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_179,s2_78,s2_83,s2_195], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_179) (b2_179 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_78) (b2_78 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_83) (b2_83 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_195) (b2_195 theta) <|
    PetersenLocalChildren.nil
theorem b1_1 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_1 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa),(0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 10 s1_1 pair
  exact PetersenLocalChildren.push (pair1_1_0 theta) <|
    PetersenLocalChildren.push (pair1_1_1 theta) <|
    PetersenLocalChildren.push (pair1_1_2 theta) <|
    PetersenLocalChildren.push (pair1_1_3 theta) <|
    PetersenLocalChildren.push (pair1_1_4 theta) <|
    PetersenLocalChildren.push (pair1_1_5 theta) <|
    PetersenLocalChildren.push (pair1_1_6 theta) <|
    PetersenLocalChildren.push (pair1_1_7 theta) <|
    PetersenLocalChildren.push (pair1_1_8 theta) <|
    PetersenLocalChildren.push (pair1_1_9 theta) <|
    PetersenLocalChildren.push (pair1_1_10 theta) <|
    PetersenLocalChildren.push (pair1_1_11 theta) <|
    PetersenLocalChildren.push (pair1_1_12 theta) <|
    PetersenLocalChildren.push (pair1_1_13 theta) <|
    PetersenLocalChildren.push (pair1_1_14 theta) <|
    PetersenLocalChildren.push (pair1_1_15 theta) <|
    PetersenLocalChildren.push (pair1_1_16 theta) <|
    PetersenLocalChildren.push (pair1_1_17 theta) <|
    PetersenLocalChildren.push (pair1_1_18 theta) <|
    PetersenLocalChildren.push (pair1_1_19 theta) <|
    PetersenLocalChildren.push (pair1_1_20 theta) <|
    PetersenLocalChildren.push (pair1_1_21 theta) <|
    PetersenLocalChildren.push (pair1_1_22 theta) <|
    PetersenLocalChildren.push (pair1_1_23 theta) <|
    PetersenLocalChildren.push (pair1_1_24 theta) <|
    PetersenLocalChildren.push (pair1_1_25 theta) <|
    PetersenLocalChildren.push (pair1_1_26 theta) <|
    PetersenLocalChildren.push (pair1_1_27 theta) <|
    PetersenLocalChildren.push (pair1_1_28 theta) <|
    PetersenLocalChildren.push (pair1_1_29 theta) <|
    PetersenLocalChildren.push (pair1_1_30 theta) <|
    PetersenLocalChildren.push (pair1_1_31 theta) <|
    PetersenLocalChildren.push (pair1_1_32 theta) <|
    PetersenLocalChildren.push (pair1_1_33 theta) <|
    PetersenLocalChildren.push (pair1_1_34 theta) <|
    PetersenLocalChildren.push (pair1_1_35 theta) <|
    PetersenLocalChildren.nil
theorem b1_2 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_2 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s1_2 11 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w17 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
