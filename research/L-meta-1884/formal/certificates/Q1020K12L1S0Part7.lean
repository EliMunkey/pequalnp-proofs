import PetersenLocalChildren
import Q1020K12L1S0Local
import Q1020K12L2S0
import Q1020K12L2S1
import Q1020K12L2S4
import Q1020K12L2S5
import Q1020K12L2S6
import Q1020K12L2S7
import Q1020K12L2S8
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
private theorem pair1_19_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_379,a625,a626,s2_495]) (hints := [8484,8484,16964,0,774,774,17221,3,774,774,16964,1,8484,8484,17221,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_379,a625,a626,s2_495], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_379) (b2_379 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a625) (via sym4 fix4 (by decide +kernel) (b2_217 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a626) (via sym6 fix6 (by decide +kernel) (b2_352 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_495) (b2_495 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_393,a627,a628,s2_501]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_393,a627,a628,s2_501], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_393) (b2_393 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a627) (via sym4 fix4 (by decide +kernel) (b2_339 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a628) (via sym7 fix7 (by decide +kernel) (b2_339 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_501) (b2_501 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a629,a630,a631,a632]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a629,a630,a631,a632], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a629) (via sym1 fix1 (by decide +kernel) (b2_395 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a630) (via sym2 fix2 (by decide +kernel) (b2_336 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a631) (via sym6 fix6 (by decide +kernel) (b2_336 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a632) (via sym1 fix1 (by decide +kernel) (b2_503 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_400,s2_306,a633,a634]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_400,s2_306,a633,a634], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_400) (b2_400 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_306) (b2_306 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a633) (via sym6 fix6 (by decide +kernel) (b2_306 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a634) (via sym2 fix2 (by decide +kernel) (b2_512 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a635,a636,a637,a638]) (hints := [774,774,10252,0,8453,8484,8453,3,8452,8484,10252,1,8452,774,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a635,a636,a637,a638], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a635) (via sym1 fix1 (by decide +kernel) (b2_382 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a636) (via sym2 fix2 (by decide +kernel) (b2_214 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a637) (via sym7 fix7 (by decide +kernel) (b2_355 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a638) (via sym1 fix1 (by decide +kernel) (b2_498 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_415,a639,a640,a641,a642,a643]) (hints := [776,776,16904,0,24934,24934,4,5,16904,24934,16904,1,776,776,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_415,a639,a640,a641,a642,a643], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_415) (b2_415 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a639) (via sym1 fix1 (by decide +kernel) (b2_62 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a640) (via sym6 fix6 (by decide +kernel) (b2_327 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a641) (via sym6 fix6 (by decide +kernel) (b2_322 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a642) (via sym1 fix1 (by decide +kernel) (b2_534 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a643) (via sym5 fix5 (by decide +kernel) (b2_506 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_424,s2_423,a644,a645,a646,a647,s2_531,s2_527]) (hints := [8488,8488,0,1,778,778,6,7,778,778,2,3,8488,8488,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_424,s2_423,a644,a645,a646,a647,s2_531,s2_527], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_424) (b2_424 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_423) (b2_423 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a644) (via sym1 fix1 (by decide +kernel) (b2_17 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a645) (via sym1 fix1 (by decide +kernel) (b2_18 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a646) (via sym6 fix6 (by decide +kernel) (b2_359 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a647) (via sym6 fix6 (by decide +kernel) (b2_358 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_531) (b2_531 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_527) (b2_527 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a648,s2_59,a649,a650]) (hints := [774,774,33800,0,33801,33670,34057,3,33542,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a648,s2_59,a649,a650], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a648) (via sym1 fix1 (by decide +kernel) (b2_418 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_59) (b2_59 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a649) (via sym7 fix7 (by decide +kernel) (b2_325 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a650) (via sym3 fix3 (by decide +kernel) (b2_509 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a651,a652,a653,a654]) (hints := [16964,16964,33924,0,1542,17992,1542,3,17988,17992,33924,1,1542,16964,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a651,a652,a653,a654], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a651) (via sym2 fix2 (by decide +kernel) (b2_379 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a652) (via sym5 fix5 (by decide +kernel) (b2_352 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a653) (via sym7 fix7 (by decide +kernel) (b2_217 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a654) (via sym2 fix2 (by decide +kernel) (b2_495 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a655,a656,a657,a658,a659,s2_506]) (hints := [10278,16966,10278,0,10792,4,10792,5,10278,1,10278,2,10792,16966,10792,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a655,a656,a657,a658,a659,s2_506], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a655) (via sym5 fix5 (by decide +kernel) (b2_415 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a656) (via sym2 fix2 (by decide +kernel) (b2_327 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a657) (via sym2 fix2 (by decide +kernel) (b2_322 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a658) (via sym4 fix4 (by decide +kernel) (b2_62 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a659) (via sym4 fix4 (by decide +kernel) (b2_534 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_506) (b2_506 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a660,s2_327,s2_322,a661,a662,a663]) (hints := [16966,16966,20550,0,37512,4,37512,5,20550,1,20550,2,16966,16966,37512,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a660,s2_327,s2_322,a661,a662,a663], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a660) (via sym6 fix6 (by decide +kernel) (b2_415 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_327) (b2_327 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_322) (b2_322 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a661) (via sym7 fix7 (by decide +kernel) (b2_62 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a662) (via sym7 fix7 (by decide +kernel) (b2_534 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a663) (via sym2 fix2 (by decide +kernel) (b2_506 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_455,a664,a665,s2_519]) (hints := [8453,16964,8453,0,10766,25188,10766,3,8453,25188,8453,1,10766,16964,10766,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_455,a664,a665,s2_519], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_455) (b2_455 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a664) (via sym2 fix2 (by decide +kernel) (b2_183 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a665) (via sym4 fix4 (by decide +kernel) (b2_194 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_519) (b2_519 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a430,s2_481,s2_477,a666,a667,a668,a669]) (hints := [18449,0,1,2,16967,16967,3,4,16905,5,16905,6]) (by decide +kernel) ?_
  change ∀ V ∈ [a430,s2_481,s2_477,a666,a667,a668,a669], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a430) (via sym5 fix5 (by decide +kernel) (b2_481 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_481) (b2_481 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_477) (b2_477 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a666) (via sym1 fix1 (by decide +kernel) (b2_277 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a667) (via sym1 fix1 (by decide +kernel) (b2_276 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a668) (via sym4 fix4 (by decide +kernel) (b2_277 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a669) (via sym4 fix4 (by decide +kernel) (b2_276 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a668,a669,s2_6,s2_5,a407]) (hints := [774,16965,2,3,774,0,4,1]) (by decide +kernel) ?_
  change ∀ V ∈ [a668,a669,s2_6,s2_5,a407], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a668) (via sym4 fix4 (by decide +kernel) (b2_277 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a669) (via sym4 fix4 (by decide +kernel) (b2_276 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_5) (b2_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a407) (via sym4 fix4 (by decide +kernel) (b2_272 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a670,s2_183,a671,a672]) (hints := [33800,16964,33800,0,37398,49860,37398,3,33800,49860,33800,1,37398,16964,37398,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a670,s2_183,a671,a672], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a670) (via sym2 fix2 (by decide +kernel) (b2_455 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_183) (b2_183 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a671) (via sym7 fix7 (by decide +kernel) (b2_194 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a672) (via sym2 fix2 (by decide +kernel) (b2_519 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a673,a674,a675,s2_512]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a673,a674,a675,s2_512], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a673) (via sym2 fix2 (by decide +kernel) (b2_400 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a674) (via sym2 fix2 (by decide +kernel) (b2_306 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a675) (via sym5 fix5 (by decide +kernel) (b2_306 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_512) (b2_512 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a676,s2_336,a677,a678]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a676,s2_336,a677,a678], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a676) (via sym3 fix3 (by decide +kernel) (b2_395 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_336) (b2_336 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a677) (via sym5 fix5 (by decide +kernel) (b2_336 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a678) (via sym3 fix3 (by decide +kernel) (b2_503 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a679,a680,a681,a682]) (hints := [8453,1542,8453,0,8457,9766,9481,3,8453,9766,8453,1,9477,1542,9481,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a679,a680,a681,a682], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a679) (via sym3 fix3 (by decide +kernel) (b2_418 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a680) (via sym2 fix2 (by decide +kernel) (b2_59 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a681) (via sym4 fix4 (by decide +kernel) (b2_325 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a682) (via sym1 fix1 (by decide +kernel) (b2_509 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a683,a684,a685,a686,a687,a688]) (hints := [1544,1544,16904,0,50374,50374,4,5,16904,50374,16904,1,1544,1544,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a683,a684,a685,a686,a687,a688], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a683) (via sym2 fix2 (by decide +kernel) (b2_415 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a684) (via sym3 fix3 (by decide +kernel) (b2_62 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a685) (via sym5 fix5 (by decide +kernel) (b2_327 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a686) (via sym5 fix5 (by decide +kernel) (b2_322 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a687) (via sym3 fix3 (by decide +kernel) (b2_534 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a688) (via sym6 fix6 (by decide +kernel) (b2_506 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a689,a690,a691,a692,a693,a694,a695,a696]) (hints := [33928,33928,0,1,1546,1546,6,7,1546,1546,2,3,33928,33928,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a689,a690,a691,a692,a693,a694,a695,a696], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a689) (via sym2 fix2 (by decide +kernel) (b2_424 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a690) (via sym2 fix2 (by decide +kernel) (b2_423 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a691) (via sym3 fix3 (by decide +kernel) (b2_17 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a692) (via sym3 fix3 (by decide +kernel) (b2_18 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a693) (via sym5 fix5 (by decide +kernel) (b2_359 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a694) (via sym5 fix5 (by decide +kernel) (b2_358 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a695) (via sym2 fix2 (by decide +kernel) (b2_531 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a696) (via sym2 fix2 (by decide +kernel) (b2_527 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a697,s2_214,a698,a699]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a697,s2_214,a698,a699], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a697) (via sym3 fix3 (by decide +kernel) (b2_382 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_214) (b2_214 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a698) (via sym4 fix4 (by decide +kernel) (b2_355 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a699) (via sym3 fix3 (by decide +kernel) (b2_498 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a700,a701,a702,a703]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a700,a701,a702,a703], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a700) (via sym5 fix5 (by decide +kernel) (b2_393 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a701) (via sym1 fix1 (by decide +kernel) (b2_339 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a702) (via sym3 fix3 (by decide +kernel) (b2_339 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a703) (via sym5 fix5 (by decide +kernel) (b2_501 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a704,a705,a706,a707]) (hints := [8453,18500,8453,0,10252,10276,10252,3,10244,10276,8453,1,10244,18500,10252,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a704,a705,a706,a707], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a704) (via sym4 fix4 (by decide +kernel) (b2_382 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a705) (via sym6 fix6 (by decide +kernel) (b2_214 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a706) (via sym3 fix3 (by decide +kernel) (b2_355 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a707) (via sym4 fix4 (by decide +kernel) (b2_498 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a708,a709,a710,a711]) (hints := [16902,10276,16902,0,16910,18500,18958,3,16902,18500,16902,1,18950,10276,18958,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a708,a709,a710,a711], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a708) (via sym5 fix5 (by decide +kernel) (b2_379 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a709) (via sym1 fix1 (by decide +kernel) (b2_217 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a710) (via sym2 fix2 (by decide +kernel) (b2_352 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a711) (via sym5 fix5 (by decide +kernel) (b2_495 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a712,a713,a714,a715,a716,a717,a718,a719]) (hints := [10280,10280,0,1,10794,10794,6,7,10794,10794,2,3,10280,10280,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a712,a713,a714,a715,a716,a717,a718,a719], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a712) (via sym5 fix5 (by decide +kernel) (b2_424 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a713) (via sym5 fix5 (by decide +kernel) (b2_423 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a714) (via sym4 fix4 (by decide +kernel) (b2_17 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a715) (via sym4 fix4 (by decide +kernel) (b2_18 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a716) (via sym2 fix2 (by decide +kernel) (b2_359 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a717) (via sym2 fix2 (by decide +kernel) (b2_358 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a718) (via sym5 fix5 (by decide +kernel) (b2_531 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a719) (via sym5 fix5 (by decide +kernel) (b2_527 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a720,a721,a722,a723]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a720,a721,a722,a723], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a720) (via sym4 fix4 (by decide +kernel) (b2_418 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a721) (via sym5 fix5 (by decide +kernel) (b2_59 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a722) (via sym3 fix3 (by decide +kernel) (b2_325 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a723) (via sym7 fix7 (by decide +kernel) (b2_509 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a724,a725,a726,a727]) (hints := [8453,20548,8453,0,8469,28772,12565,3,8453,28772,8453,1,12549,20548,12565,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a724,a725,a726,a727], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a724) (via sym7 fix7 (by decide +kernel) (b2_418 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a725) (via sym6 fix6 (by decide +kernel) (b2_59 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a726) (via sym1 fix1 (by decide +kernel) (b2_325 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a727) (via sym4 fix4 (by decide +kernel) (b2_509 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a728,a729,s2_352,a730]) (hints := [16902,36996,16902,0,16918,20548,21014,3,16902,20548,16902,1,20998,36996,21014,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a728,a729,s2_352,a730], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a728) (via sym6 fix6 (by decide +kernel) (b2_379 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a729) (via sym3 fix3 (by decide +kernel) (b2_217 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_352) (b2_352 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a730) (via sym6 fix6 (by decide +kernel) (b2_495 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a731,a732,a733,a734,s2_359,s2_358,a735,a736]) (hints := [37000,37000,0,1,20552,20552,6,7,20552,20552,2,3,37000,37000,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a731,a732,a733,a734,s2_359,s2_358,a735,a736], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a731) (via sym6 fix6 (by decide +kernel) (b2_424 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a732) (via sym6 fix6 (by decide +kernel) (b2_423 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a733) (via sym7 fix7 (by decide +kernel) (b2_17 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a734) (via sym7 fix7 (by decide +kernel) (b2_18 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_359) (b2_359 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_358) (b2_358 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a735) (via sym6 fix6 (by decide +kernel) (b2_531 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a736) (via sym6 fix6 (by decide +kernel) (b2_527 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a737,a738,a739,a740]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a737,a738,a739,a740], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a737) (via sym7 fix7 (by decide +kernel) (b2_382 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a738) (via sym5 fix5 (by decide +kernel) (b2_214 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a739) (via sym1 fix1 (by decide +kernel) (b2_355 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a740) (via sym7 fix7 (by decide +kernel) (b2_498 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a741,a742,a743,a744]) (hints := [8453,8453,16902,0,16934,24901,25126,3,16902,24901,16902,1,8453,8453,25126,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a741,a742,a743,a744], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a741) (via sym5 fix5 (by decide +kernel) (b2_455 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a742) (via sym1 fix1 (by decide +kernel) (b2_194 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a743) (via sym6 fix6 (by decide +kernel) (b2_183 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a744) (via sym5 fix5 (by decide +kernel) (b2_519 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a745,a746,a747,a748,a749,a750,s2_532,s2_528]) (hints := [8457,8457,0,1,10770,10770,6,7,10770,10770,2,3,8457,8457,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a745,a746,a747,a748,a749,a750,s2_532,s2_528], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a745) (via sym1 fix1 (by decide +kernel) (b2_486 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a746) (via sym1 fix1 (by decide +kernel) (b2_487 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a747) (via sym1 fix1 (by decide +kernel) (b2_20 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a748) (via sym1 fix1 (by decide +kernel) (b2_21 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a749) (via sym2 fix2 (by decide +kernel) (b2_282 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a750) (via sym2 fix2 (by decide +kernel) (b2_281 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_532) (b2_532 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_528) (b2_528 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a751,s2_271,a752,s2_530]) (hints := [8453,8453,33800,0,40996,41092,40996,3,40964,41092,33800,1,40964,8453,40996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a751,s2_271,a752,s2_530], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a751) (via sym1 fix1 (by decide +kernel) (b2_479 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_271) (b2_271 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a752) (via sym2 fix2 (by decide +kernel) (b2_271 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_530) (b2_530 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_19_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a666,a667,s2_6,s2_5,a364]) (hints := [16903,16903,2,3,18445,0,4,1]) (by decide +kernel) ?_
  change ∀ V ∈ [a666,a667,s2_6,s2_5,a364], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a666) (via sym1 fix1 (by decide +kernel) (b2_277 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a667) (via sym1 fix1 (by decide +kernel) (b2_276 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_5) (b2_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a364) (via sym1 fix1 (by decide +kernel) (b2_272 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a753,a754,a755,a756]) (hints := [16902,16902,33800,0,50248,49798,50248,3,49670,49798,33800,1,16902,16902,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a753,a754,a755,a756], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a753) (via sym6 fix6 (by decide +kernel) (b2_455 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a754) (via sym5 fix5 (by decide +kernel) (b2_183 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a755) (via sym3 fix3 (by decide +kernel) (b2_194 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a756) (via sym6 fix6 (by decide +kernel) (b2_519 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_19_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_19 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a757,a758,s2_282,s2_281,a759,a760,a761,a762]) (hints := [33804,0,33804,1,37402,6,37402,7,33804,2,33804,3,37402,4,37402,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a757,a758,s2_282,s2_281,a759,a760,a761,a762], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a757) (via sym3 fix3 (by decide +kernel) (b2_486 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a758) (via sym3 fix3 (by decide +kernel) (b2_487 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_282) (b2_282 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_281) (b2_281 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a759) (via sym3 fix3 (by decide +kernel) (b2_20 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a760) (via sym3 fix3 (by decide +kernel) (b2_21 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a761) (via sym2 fix2 (by decide +kernel) (b2_532 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a762) (via sym2 fix2 (by decide +kernel) (b2_528 theta)) <|
    PetersenLocalChildren.nil
theorem b1_19 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_19 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 10 s1_19 pair
  exact PetersenLocalChildren.push (pair1_19_0 theta) <|
    PetersenLocalChildren.push (pair1_19_1 theta) <|
    PetersenLocalChildren.push (pair1_19_2 theta) <|
    PetersenLocalChildren.push (pair1_19_3 theta) <|
    PetersenLocalChildren.push (pair1_19_4 theta) <|
    PetersenLocalChildren.push (pair1_19_5 theta) <|
    PetersenLocalChildren.push (pair1_19_6 theta) <|
    PetersenLocalChildren.push (pair1_19_7 theta) <|
    PetersenLocalChildren.push (pair1_19_8 theta) <|
    PetersenLocalChildren.push (pair1_19_9 theta) <|
    PetersenLocalChildren.push (pair1_19_10 theta) <|
    PetersenLocalChildren.push (pair1_19_11 theta) <|
    PetersenLocalChildren.push (pair1_19_12 theta) <|
    PetersenLocalChildren.push (pair1_19_13 theta) <|
    PetersenLocalChildren.push (pair1_19_14 theta) <|
    PetersenLocalChildren.push (pair1_19_15 theta) <|
    PetersenLocalChildren.push (pair1_19_16 theta) <|
    PetersenLocalChildren.push (pair1_19_17 theta) <|
    PetersenLocalChildren.push (pair1_19_18 theta) <|
    PetersenLocalChildren.push (pair1_19_19 theta) <|
    PetersenLocalChildren.push (pair1_19_20 theta) <|
    PetersenLocalChildren.push (pair1_19_21 theta) <|
    PetersenLocalChildren.push (pair1_19_22 theta) <|
    PetersenLocalChildren.push (pair1_19_23 theta) <|
    PetersenLocalChildren.push (pair1_19_24 theta) <|
    PetersenLocalChildren.push (pair1_19_25 theta) <|
    PetersenLocalChildren.push (pair1_19_26 theta) <|
    PetersenLocalChildren.push (pair1_19_27 theta) <|
    PetersenLocalChildren.push (pair1_19_28 theta) <|
    PetersenLocalChildren.push (pair1_19_29 theta) <|
    PetersenLocalChildren.push (pair1_19_30 theta) <|
    PetersenLocalChildren.push (pair1_19_31 theta) <|
    PetersenLocalChildren.push (pair1_19_32 theta) <|
    PetersenLocalChildren.push (pair1_19_33 theta) <|
    PetersenLocalChildren.push (pair1_19_34 theta) <|
    PetersenLocalChildren.push (pair1_19_35 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
