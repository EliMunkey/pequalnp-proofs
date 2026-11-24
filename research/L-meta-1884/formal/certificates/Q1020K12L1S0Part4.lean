import PetersenLocalChildren
import Q1020K12L1S0Local
import Q1020K12L2S0
import Q1020K12L2S1
import Q1020K12L2S3
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
private theorem pair1_13_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_369,s2_368,a338,a339,a340,a341,a342,a343,a344,a345,s2_492,s2_466]) (hints := [782,782,0,1,8,9,10,11,2,3,4,5,782,782,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_369,s2_368,a338,a339,a340,a341,a342,a343,a344,a345,s2_492,s2_466], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_369) (b2_369 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_368) (b2_368 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a338) (via sym1 fix1 (by decide +kernel) (b2_296 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a339) (via sym1 fix1 (by decide +kernel) (b2_295 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a340) (via sym1 fix1 (by decide +kernel) (b2_294 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a341) (via sym1 fix1 (by decide +kernel) (b2_293 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a342) (via sym6 fix6 (by decide +kernel) (b2_312 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a343) (via sym6 fix6 (by decide +kernel) (b2_311 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a344) (via sym6 fix6 (by decide +kernel) (b2_540 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a345) (via sym6 fix6 (by decide +kernel) (b2_482 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_492) (b2_492 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_466) (b2_466 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_373,a346,a347,s2_467]) (hints := [1544,8484,1544,0,773,774,773,3,772,774,1544,1,772,8484,773,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_373,a346,a347,s2_467], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_373) (b2_373 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a346) (via sym4 fix4 (by decide +kernel) (b2_211 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a347) (via sym6 fix6 (by decide +kernel) (b2_346 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_467) (b2_467 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_389,a348,a349,s2_468]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_389,a348,a349,s2_468], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_389) (b2_389 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a348) (via sym4 fix4 (by decide +kernel) (b2_333 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a349) (via sym7 fix7 (by decide +kernel) (b2_333 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_468) (b2_468 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a350,a351,a352,s2_469]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a350,a351,a352,s2_469], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a350) (via sym1 fix1 (by decide +kernel) (b2_391 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a351) (via sym2 fix2 (by decide +kernel) (b2_330 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a352) (via sym6 fix6 (by decide +kernel) (b2_330 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_469) (b2_469 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_397,s2_302,a353,a354]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_397,s2_302,a353,a354], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_397) (b2_397 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_302) (b2_302 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a353) (via sym6 fix6 (by decide +kernel) (b2_302 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a354) (via sym2 fix2 (by decide +kernel) (b2_471 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a355,a356,a357,s2_473]) (hints := [774,774,10252,0,8453,8484,8453,3,8452,8484,10252,1,8452,774,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a355,a356,a357,s2_473], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a355) (via sym1 fix1 (by decide +kernel) (b2_376 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a356) (via sym2 fix2 (by decide +kernel) (b2_208 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a357) (via sym7 fix7 (by decide +kernel) (b2_349 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_473) (b2_473 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_409,a358,a359,a360]) (hints := [774,774,18444,0,18445,24932,18701,3,18444,24932,18444,1,774,774,18701,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_409,a358,a359,a360], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_409) (b2_409 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a358) (via sym1 fix1 (by decide +kernel) (b2_56 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a359) (via sym6 fix6 (by decide +kernel) (b2_316 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a360) (via sym5 fix5 (by decide +kernel) (b2_470 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a361,s2_53,a362,a363]) (hints := [774,774,33800,0,33801,33670,34057,3,33542,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a361,s2_53,a362,a363], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a361) (via sym1 fix1 (by decide +kernel) (b2_412 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_53) (b2_53 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a362) (via sym7 fix7 (by decide +kernel) (b2_319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a363) (via sym2 fix2 (by decide +kernel) (b2_476 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_3,a364,a365,a366]) (hints := [774,0,774,1,16965,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_3,a364,a365,a366], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_3) (b2_3 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a364) (via sym1 fix1 (by decide +kernel) (b2_272 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a365) (via sym1 fix1 (by decide +kernel) (b2_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a366) (via sym1 fix1 (by decide +kernel) (b2_266 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a367,a368,a369,a370,a371,a372,a373,a374,a375,a376,a377,a378]) (hints := [1550,0,1550,1,8,9,10,11,1550,2,1550,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [a367,a368,a369,a370,a371,a372,a373,a374,a375,a376,a377,a378], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a367) (via sym2 fix2 (by decide +kernel) (b2_369 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a368) (via sym2 fix2 (by decide +kernel) (b2_368 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a369) (via sym5 fix5 (by decide +kernel) (b2_312 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a370) (via sym5 fix5 (by decide +kernel) (b2_311 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a371) (via sym3 fix3 (by decide +kernel) (b2_296 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a372) (via sym3 fix3 (by decide +kernel) (b2_294 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a373) (via sym3 fix3 (by decide +kernel) (b2_295 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a374) (via sym3 fix3 (by decide +kernel) (b2_293 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a375) (via sym5 fix5 (by decide +kernel) (b2_540 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a376) (via sym2 fix2 (by decide +kernel) (b2_492 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a377) (via sym5 fix5 (by decide +kernel) (b2_482 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a378) (via sym2 fix2 (by decide +kernel) (b2_466 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a379,a380,a381,a382,a383,a384,a385,a386,a387,a388,a389,a390]) (hints := [10284,0,10284,1,8,9,10,11,10284,2,10284,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [a379,a380,a381,a382,a383,a384,a385,a386,a387,a388,a389,a390], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a379) (via sym5 fix5 (by decide +kernel) (b2_369 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a380) (via sym5 fix5 (by decide +kernel) (b2_368 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a381) (via sym2 fix2 (by decide +kernel) (b2_312 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a382) (via sym2 fix2 (by decide +kernel) (b2_311 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a383) (via sym4 fix4 (by decide +kernel) (b2_296 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a384) (via sym4 fix4 (by decide +kernel) (b2_294 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a385) (via sym4 fix4 (by decide +kernel) (b2_295 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a386) (via sym4 fix4 (by decide +kernel) (b2_293 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a387) (via sym2 fix2 (by decide +kernel) (b2_540 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a388) (via sym5 fix5 (by decide +kernel) (b2_492 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a389) (via sym2 fix2 (by decide +kernel) (b2_482 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a390) (via sym5 fix5 (by decide +kernel) (b2_466 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a391,a392,s2_312,s2_311,a393,a394,a395,a396,s2_540,a397,s2_482,a398]) (hints := [20556,0,20556,1,8,9,10,11,20556,2,20556,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [a391,a392,s2_312,s2_311,a393,a394,a395,a396,s2_540,a397,s2_482,a398], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a391) (via sym6 fix6 (by decide +kernel) (b2_369 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a392) (via sym6 fix6 (by decide +kernel) (b2_368 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_312) (b2_312 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_311) (b2_311 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a393) (via sym7 fix7 (by decide +kernel) (b2_296 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a394) (via sym7 fix7 (by decide +kernel) (b2_294 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a395) (via sym7 fix7 (by decide +kernel) (b2_295 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a396) (via sym7 fix7 (by decide +kernel) (b2_293 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_540) (b2_540 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a397) (via sym6 fix6 (by decide +kernel) (b2_492 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_482) (b2_482 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a398) (via sym6 fix6 (by decide +kernel) (b2_466 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_437,s2_436,a399,a400,a401,a402,a403,a404,a405,s2_515,a406,s2_474]) (hints := [8461,0,8461,1,8,9,10,11,8461,2,8461,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_437,s2_436,a399,a400,a401,a402,a403,a404,a405,s2_515,a406,s2_474], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_437) (b2_437 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_436) (b2_436 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a399) (via sym2 fix2 (by decide +kernel) (b2_74 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a400) (via sym2 fix2 (by decide +kernel) (b2_73 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a401) (via sym1 fix1 (by decide +kernel) (b2_300 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a402) (via sym1 fix1 (by decide +kernel) (b2_298 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a403) (via sym1 fix1 (by decide +kernel) (b2_299 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a404) (via sym1 fix1 (by decide +kernel) (b2_297 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a405) (via sym2 fix2 (by decide +kernel) (b2_535 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_515) (b2_515 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a406) (via sym2 fix2 (by decide +kernel) (b2_480 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_474) (b2_474 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_3,a407,a408,a409]) (hints := [16903,0,18445,1,16903,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_3,a407,a408,a409], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_3) (b2_3 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a407) (via sym4 fix4 (by decide +kernel) (b2_272 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a408) (via sym4 fix4 (by decide +kernel) (b2_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a409) (via sym4 fix4 (by decide +kernel) (b2_266 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a410,a411,s2_74,s2_73,a412,a413,a414,a415,s2_535,a416,s2_480,a417]) (hints := [33808,0,33808,1,8,9,10,11,33808,2,33808,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [a410,a411,s2_74,s2_73,a412,a413,a414,a415,s2_535,a416,s2_480,a417], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a410) (via sym2 fix2 (by decide +kernel) (b2_437 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a411) (via sym2 fix2 (by decide +kernel) (b2_436 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_74) (b2_74 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_73) (b2_73 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a412) (via sym3 fix3 (by decide +kernel) (b2_300 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a413) (via sym3 fix3 (by decide +kernel) (b2_298 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a414) (via sym3 fix3 (by decide +kernel) (b2_299 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a415) (via sym3 fix3 (by decide +kernel) (b2_297 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_535) (b2_535 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a416) (via sym2 fix2 (by decide +kernel) (b2_515 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_480) (b2_480 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a417) (via sym2 fix2 (by decide +kernel) (b2_474 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a418,a419,a420,a421]) (hints := [773,773,33924,0,1542,1544,1542,3,1540,1544,33924,1,1540,773,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a418,a419,a420,a421], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a418) (via sym2 fix2 (by decide +kernel) (b2_373 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a419) (via sym5 fix5 (by decide +kernel) (b2_346 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a420) (via sym7 fix7 (by decide +kernel) (b2_211 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a421) (via sym2 fix2 (by decide +kernel) (b2_467 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a422,a423,a424,s2_470]) (hints := [773,773,10276,0,781,2829,10790,3,2821,2829,10276,1,773,773,10790,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a422,a423,a424,s2_470], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a422) (via sym5 fix5 (by decide +kernel) (b2_409 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a423) (via sym2 fix2 (by decide +kernel) (b2_316 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a424) (via sym4 fix4 (by decide +kernel) (b2_56 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_470) (b2_470 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a425,s2_316,a426,a427]) (hints := [773,773,20548,0,789,4885,37510,3,4869,4885,20548,1,773,773,37510,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a425,s2_316,a426,a427], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a425) (via sym6 fix6 (by decide +kernel) (b2_409 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_316) (b2_316 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a426) (via sym7 fix7 (by decide +kernel) (b2_56 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a427) (via sym2 fix2 (by decide +kernel) (b2_470 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_438,a428,a429,s2_475]) (hints := [773,773,8453,0,10254,9768,10766,3,8453,9768,8453,1,773,773,10766,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_438,a428,a429,s2_475], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_438) (b2_438 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a428) (via sym2 fix2 (by decide +kernel) (b2_138 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a429) (via sym4 fix4 (by decide +kernel) (b2_171 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_475) (b2_475 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a365,a366,a408,a409,a430,s2_481,s2_477]) (hints := [18449,4,5,6,18447,0,18447,1,776,776,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a365,a366,a408,a409,a430,s2_481,s2_477], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a365) (via sym1 fix1 (by decide +kernel) (b2_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a366) (via sym1 fix1 (by decide +kernel) (b2_266 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a408) (via sym4 fix4 (by decide +kernel) (b2_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a409) (via sym4 fix4 (by decide +kernel) (b2_266 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a430) (via sym5 fix5 (by decide +kernel) (b2_481 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_481) (b2_481 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_477) (b2_477 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a431,s2_138,a432,a433]) (hints := [773,773,33800,0,36886,33669,37398,3,33541,33669,33800,1,773,773,37398,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a431,s2_138,a432,a433], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a431) (via sym2 fix2 (by decide +kernel) (b2_438 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_138) (b2_138 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a432) (via sym7 fix7 (by decide +kernel) (b2_171 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a433) (via sym2 fix2 (by decide +kernel) (b2_475 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a434,a435,a436,s2_471]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a434,a435,a436,s2_471], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a434) (via sym2 fix2 (by decide +kernel) (b2_397 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a435) (via sym2 fix2 (by decide +kernel) (b2_302 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a436) (via sym5 fix5 (by decide +kernel) (b2_302 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_471) (b2_471 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a437,s2_330,a438,a439]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a437,s2_330,a438,a439], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a437) (via sym3 fix3 (by decide +kernel) (b2_391 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_330) (b2_330 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a438) (via sym5 fix5 (by decide +kernel) (b2_330 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a439) (via sym2 fix2 (by decide +kernel) (b2_469 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a440,a441,a442,s2_476]) (hints := [8453,1542,8453,0,8457,9766,9481,3,8453,9766,8453,1,9477,1542,9481,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a440,a441,a442,s2_476], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a440) (via sym3 fix3 (by decide +kernel) (b2_412 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a441) (via sym2 fix2 (by decide +kernel) (b2_53 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a442) (via sym4 fix4 (by decide +kernel) (b2_319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_476) (b2_476 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a443,a444,a445,a446]) (hints := [1542,1542,18444,0,18448,50372,19472,3,18444,50372,18444,1,1542,1542,19472,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a443,a444,a445,a446], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a443) (via sym2 fix2 (by decide +kernel) (b2_409 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a444) (via sym3 fix3 (by decide +kernel) (b2_56 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a445) (via sym5 fix5 (by decide +kernel) (b2_316 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a446) (via sym6 fix6 (by decide +kernel) (b2_470 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a447,s2_208,a448,a449]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a447,s2_208,a448,a449], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a447) (via sym3 fix3 (by decide +kernel) (b2_376 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_208) (b2_208 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a448) (via sym4 fix4 (by decide +kernel) (b2_349 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a449) (via sym2 fix2 (by decide +kernel) (b2_473 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a450,a451,a452,a453]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a450,a451,a452,a453], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a450) (via sym5 fix5 (by decide +kernel) (b2_389 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a451) (via sym1 fix1 (by decide +kernel) (b2_333 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a452) (via sym3 fix3 (by decide +kernel) (b2_333 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a453) (via sym5 fix5 (by decide +kernel) (b2_468 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a454,a455,a456,a457]) (hints := [8453,18500,8453,0,10252,10276,10252,3,10244,10276,8453,1,10244,18500,10252,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a454,a455,a456,a457], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a454) (via sym4 fix4 (by decide +kernel) (b2_376 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a455) (via sym6 fix6 (by decide +kernel) (b2_208 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a456) (via sym3 fix3 (by decide +kernel) (b2_349 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a457) (via sym5 fix5 (by decide +kernel) (b2_473 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a458,a459,a460,a461]) (hints := [20500,10276,20500,0,18444,18500,18444,3,18436,18500,20500,1,18436,10276,18444,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a458,a459,a460,a461], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a458) (via sym5 fix5 (by decide +kernel) (b2_373 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a459) (via sym1 fix1 (by decide +kernel) (b2_211 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a460) (via sym2 fix2 (by decide +kernel) (b2_346 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a461) (via sym5 fix5 (by decide +kernel) (b2_467 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a462,a463,a464,a465]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a462,a463,a464,a465], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a462) (via sym4 fix4 (by decide +kernel) (b2_412 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a463) (via sym5 fix5 (by decide +kernel) (b2_53 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a464) (via sym3 fix3 (by decide +kernel) (b2_319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a465) (via sym6 fix6 (by decide +kernel) (b2_476 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a466,a467,a468,a469]) (hints := [8453,20548,8453,0,8469,28772,12565,3,8453,28772,8453,1,12549,20548,12565,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a466,a467,a468,a469], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a466) (via sym7 fix7 (by decide +kernel) (b2_412 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a467) (via sym6 fix6 (by decide +kernel) (b2_53 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a468) (via sym1 fix1 (by decide +kernel) (b2_319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a469) (via sym5 fix5 (by decide +kernel) (b2_476 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a470,a471,s2_346,a472]) (hints := [18444,36996,18444,0,20500,20548,20500,3,20484,20548,18444,1,20484,36996,20500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a470,a471,s2_346,a472], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a470) (via sym6 fix6 (by decide +kernel) (b2_373 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a471) (via sym3 fix3 (by decide +kernel) (b2_211 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_346) (b2_346 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a472) (via sym6 fix6 (by decide +kernel) (b2_467 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a473,a474,a475,a476]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a473,a474,a475,a476], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a473) (via sym7 fix7 (by decide +kernel) (b2_376 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a474) (via sym5 fix5 (by decide +kernel) (b2_208 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a475) (via sym1 fix1 (by decide +kernel) (b2_349 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a476) (via sym6 fix6 (by decide +kernel) (b2_473 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a477,a478,a479,a480]) (hints := [8453,8453,18444,0,20532,24901,28724,3,24837,24901,18444,1,8453,8453,28724,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a477,a478,a479,a480], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a477) (via sym5 fix5 (by decide +kernel) (b2_438 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a478) (via sym1 fix1 (by decide +kernel) (b2_171 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a479) (via sym6 fix6 (by decide +kernel) (b2_138 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a480) (via sym5 fix5 (by decide +kernel) (b2_475 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_13_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_472,s2_249,a481,s2_479]) (hints := [8453,8453,33800,0,40996,41092,40996,3,40964,41092,33800,1,40964,8453,40996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_472,s2_249,a481,s2_479], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_472) (b2_472 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_249) (b2_249 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a481) (via sym2 fix2 (by decide +kernel) (b2_249 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_479) (b2_479 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_13_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_13 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a482,a483,a484,a485]) (hints := [33800,18444,33800,0,33864,51340,50248,3,33800,51340,33800,1,50184,18444,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a482,a483,a484,a485], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a482) (via sym6 fix6 (by decide +kernel) (b2_438 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a483) (via sym5 fix5 (by decide +kernel) (b2_138 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a484) (via sym3 fix3 (by decide +kernel) (b2_171 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a485) (via sym6 fix6 (by decide +kernel) (b2_475 theta)) <|
    PetersenLocalChildren.nil
theorem b1_13 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_13 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 10 s1_13 pair
  exact PetersenLocalChildren.push (pair1_13_0 theta) <|
    PetersenLocalChildren.push (pair1_13_1 theta) <|
    PetersenLocalChildren.push (pair1_13_2 theta) <|
    PetersenLocalChildren.push (pair1_13_3 theta) <|
    PetersenLocalChildren.push (pair1_13_4 theta) <|
    PetersenLocalChildren.push (pair1_13_5 theta) <|
    PetersenLocalChildren.push (pair1_13_6 theta) <|
    PetersenLocalChildren.push (pair1_13_7 theta) <|
    PetersenLocalChildren.push (pair1_13_8 theta) <|
    PetersenLocalChildren.push (pair1_13_9 theta) <|
    PetersenLocalChildren.push (pair1_13_10 theta) <|
    PetersenLocalChildren.push (pair1_13_11 theta) <|
    PetersenLocalChildren.push (pair1_13_12 theta) <|
    PetersenLocalChildren.push (pair1_13_13 theta) <|
    PetersenLocalChildren.push (pair1_13_14 theta) <|
    PetersenLocalChildren.push (pair1_13_15 theta) <|
    PetersenLocalChildren.push (pair1_13_16 theta) <|
    PetersenLocalChildren.push (pair1_13_17 theta) <|
    PetersenLocalChildren.push (pair1_13_18 theta) <|
    PetersenLocalChildren.push (pair1_13_19 theta) <|
    PetersenLocalChildren.push (pair1_13_20 theta) <|
    PetersenLocalChildren.push (pair1_13_21 theta) <|
    PetersenLocalChildren.push (pair1_13_22 theta) <|
    PetersenLocalChildren.push (pair1_13_23 theta) <|
    PetersenLocalChildren.push (pair1_13_24 theta) <|
    PetersenLocalChildren.push (pair1_13_25 theta) <|
    PetersenLocalChildren.push (pair1_13_26 theta) <|
    PetersenLocalChildren.push (pair1_13_27 theta) <|
    PetersenLocalChildren.push (pair1_13_28 theta) <|
    PetersenLocalChildren.push (pair1_13_29 theta) <|
    PetersenLocalChildren.push (pair1_13_30 theta) <|
    PetersenLocalChildren.push (pair1_13_31 theta) <|
    PetersenLocalChildren.push (pair1_13_32 theta) <|
    PetersenLocalChildren.push (pair1_13_33 theta) <|
    PetersenLocalChildren.push (pair1_13_34 theta) <|
    PetersenLocalChildren.push (pair1_13_35 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
