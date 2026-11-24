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
private theorem pair1_12_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_367,s2_366,a216,a217,a218,a219,s2_491,s2_440]) (hints := [778,778,0,1,9002,9002,6,7,9002,9002,2,3,778,778,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_367,s2_366,a216,a217,a218,a219,s2_491,s2_440], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_367) (b2_367 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_366) (b2_366 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a216) (via sym6 fix6 (by decide +kernel) (b2_292 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a217) (via sym6 fix6 (by decide +kernel) (b2_291 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a218) (via sym6 fix6 (by decide +kernel) (b2_344 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a219) (via sym6 fix6 (by decide +kernel) (b2_343 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_491) (b2_491 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_440) (b2_440 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_372,a220,a221,s2_441]) (hints := [1544,8484,1544,0,773,774,773,3,772,774,1544,1,772,8484,773,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_372,a220,a221,s2_441], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_372) (b2_372 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a220) (via sym4 fix4 (by decide +kernel) (b2_209 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a221) (via sym6 fix6 (by decide +kernel) (b2_351 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_441) (b2_441 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_388,a222,a223,s2_442]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_388,a222,a223,s2_442], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_388) (b2_388 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a222) (via sym4 fix4 (by decide +kernel) (b2_331 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a223) (via sym7 fix7 (by decide +kernel) (b2_335 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_442) (b2_442 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a224,a225,a226,a227]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a224,a225,a226,a227], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a224) (via sym1 fix1 (by decide +kernel) (b2_388 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a225) (via sym2 fix2 (by decide +kernel) (b2_331 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a226) (via sym6 fix6 (by decide +kernel) (b2_335 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a227) (via sym1 fix1 (by decide +kernel) (b2_442 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_396,s2_301,a228,s2_447]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_396,s2_301,a228,s2_447], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_396) (b2_396 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_301) (b2_301 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a228) (via sym6 fix6 (by decide +kernel) (b2_305 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_447) (b2_447 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a229,a230,a231,a232]) (hints := [774,774,10252,0,8453,8484,8453,3,8452,8484,10252,1,8452,774,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a229,a230,a231,a232], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a229) (via sym1 fix1 (by decide +kernel) (b2_372 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a230) (via sym2 fix2 (by decide +kernel) (b2_209 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a231) (via sym7 fix7 (by decide +kernel) (b2_351 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a232) (via sym1 fix1 (by decide +kernel) (b2_441 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_408,a233,a234,s2_453]) (hints := [774,774,16902,0,18445,24932,18701,3,16902,24932,16902,1,774,774,18701,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_408,a233,a234,s2_453], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_408) (b2_408 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a233) (via sym1 fix1 (by decide +kernel) (b2_52 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a234) (via sym6 fix6 (by decide +kernel) (b2_321 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_453) (b2_453 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a235,s2_52,a236,a237]) (hints := [774,774,33800,0,33801,33670,34057,3,33542,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a235,s2_52,a236,a237], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a235) (via sym1 fix1 (by decide +kernel) (b2_408 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_52) (b2_52 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a236) (via sym7 fix7 (by decide +kernel) (b2_321 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a237) (via sym1 fix1 (by decide +kernel) (b2_453 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_2,a238,a239,a240]) (hints := [774,0,774,1,9769,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_2,a238,a239,a240], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_2) (b2_2 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a238) (via sym2 fix2 (by decide +kernel) (b2_188 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a239) (via sym2 fix2 (by decide +kernel) (b2_140 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a240) (via sym2 fix2 (by decide +kernel) (b2_139 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a241,a242,a243,a244,a245,a246,a247,s2_443]) (hints := [1546,0,1546,1,9770,6,9770,7,1546,2,1546,3,9770,4,9770,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a241,a242,a243,a244,a245,a246,a247,s2_443], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a241) (via sym2 fix2 (by decide +kernel) (b2_371 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a242) (via sym2 fix2 (by decide +kernel) (b2_370 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a243) (via sym4 fix4 (by decide +kernel) (b2_314 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a244) (via sym4 fix4 (by decide +kernel) (b2_313 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a245) (via sym7 fix7 (by decide +kernel) (b2_290 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a246) (via sym7 fix7 (by decide +kernel) (b2_289 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a247) (via sym2 fix2 (by decide +kernel) (b2_493 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_443) (b2_443 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a248,a249,a250,a251,a252,a253,a254,a255]) (hints := [10280,0,10280,1,10794,6,10794,7,10280,2,10280,3,10794,4,10794,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a248,a249,a250,a251,a252,a253,a254,a255], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a248) (via sym4 fix4 (by decide +kernel) (b2_371 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a249) (via sym4 fix4 (by decide +kernel) (b2_370 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a250) (via sym2 fix2 (by decide +kernel) (b2_314 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a251) (via sym2 fix2 (by decide +kernel) (b2_313 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a252) (via sym6 fix6 (by decide +kernel) (b2_290 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a253) (via sym6 fix6 (by decide +kernel) (b2_289 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a254) (via sym4 fix4 (by decide +kernel) (b2_493 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a255) (via sym1 fix1 (by decide +kernel) (b2_443 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a256,a257,s2_310,s2_309,a258,a259,a260,a261,s2_539,a262,s2_463,s2_448]) (hints := [20556,0,20556,1,8,9,10,11,20556,2,20556,3,4,5,6,7]) (by decide +kernel) ?_
  change ∀ V ∈ [a256,a257,s2_310,s2_309,a258,a259,a260,a261,s2_539,a262,s2_463,s2_448], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a256) (via sym6 fix6 (by decide +kernel) (b2_407 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a257) (via sym6 fix6 (by decide +kernel) (b2_406 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_310) (b2_310 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_309) (b2_309 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a258) (via sym6 fix6 (by decide +kernel) (b2_286 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a259) (via sym6 fix6 (by decide +kernel) (b2_284 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a260) (via sym6 fix6 (by decide +kernel) (b2_285 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a261) (via sym6 fix6 (by decide +kernel) (b2_283 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_539) (b2_539 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a262) (via sym2 fix2 (by decide +kernel) (b2_504 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_463) (b2_463 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_448) (b2_448 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_2,a263,a264,a265]) (hints := [8454,0,8454,1,10767,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_2,a263,a264,a265], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_2) (b2_2 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a263) (via sym4 fix4 (by decide +kernel) (b2_188 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a264) (via sym4 fix4 (by decide +kernel) (b2_140 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a265) (via sym4 fix4 (by decide +kernel) (b2_139 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_437,s2_435,a266,a267,a268,a269,a270,s2_454]) (hints := [16906,0,16906,1,25130,6,25130,7,16906,2,16906,3,25130,4,25130,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_437,s2_435,a266,a267,a268,a269,a270,s2_454], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_437) (b2_437 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_435) (b2_435 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a266) (via sym1 fix1 (by decide +kernel) (b2_71 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a267) (via sym1 fix1 (by decide +kernel) (b2_70 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a268) (via sym6 fix6 (by decide +kernel) (b2_288 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a269) (via sym6 fix6 (by decide +kernel) (b2_287 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a270) (via sym5 fix5 (by decide +kernel) (b2_514 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_454) (b2_454 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a271,a272,s2_71,s2_70,a273,a274,a275,a276]) (hints := [33804,0,33804,1,41514,6,41514,7,33804,2,33804,3,41514,4,41514,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a271,a272,s2_71,s2_70,a273,a274,a275,a276], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a271) (via sym1 fix1 (by decide +kernel) (b2_437 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a272) (via sym1 fix1 (by decide +kernel) (b2_435 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_71) (b2_71 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_70) (b2_70 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a273) (via sym7 fix7 (by decide +kernel) (b2_288 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a274) (via sym7 fix7 (by decide +kernel) (b2_287 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a275) (via sym3 fix3 (by decide +kernel) (b2_514 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a276) (via sym1 fix1 (by decide +kernel) (b2_454 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a277,a278,a279,s2_444]) (hints := [773,773,33924,0,1542,1544,1542,3,1540,1544,33924,1,1540,773,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a277,a278,a279,s2_444], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a277) (via sym2 fix2 (by decide +kernel) (b2_374 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a278) (via sym5 fix5 (by decide +kernel) (b2_348 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a279) (via sym7 fix7 (by decide +kernel) (b2_213 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_444) (b2_444 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a280,a281,a282,s2_445]) (hints := [773,773,10276,0,781,2829,10790,3,2821,2829,10276,1,773,773,10790,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a280,a281,a282,s2_445], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a280) (via sym5 fix5 (by decide +kernel) (b2_411 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a281) (via sym2 fix2 (by decide +kernel) (b2_317 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a282) (via sym4 fix4 (by decide +kernel) (b2_54 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_445) (b2_445 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a283,s2_315,a284,s2_449]) (hints := [773,773,20548,0,789,4885,37510,3,4869,4885,20548,1,773,773,37510,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a283,s2_315,a284,s2_449], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a283) (via sym6 fix6 (by decide +kernel) (b2_414 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_315) (b2_315 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a284) (via sym7 fix7 (by decide +kernel) (b2_58 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_449) (b2_449 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a239,a240,a264,a265,a285,s2_462,s2_451]) (hints := [10257,4,5,6,8456,0,8456,1,776,776,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a239,a240,a264,a265,a285,s2_462,s2_451], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a239) (via sym2 fix2 (by decide +kernel) (b2_140 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a240) (via sym2 fix2 (by decide +kernel) (b2_139 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a264) (via sym4 fix4 (by decide +kernel) (b2_140 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a265) (via sym4 fix4 (by decide +kernel) (b2_139 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a285) (via sym1 fix1 (by decide +kernel) (b2_462 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_462) (b2_462 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_451) (b2_451 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_438,a286,a287,s2_455]) (hints := [773,773,18444,0,16902,16964,16902,3,16900,16964,18444,1,16900,773,16902,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_438,a286,a287,s2_455], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_438) (b2_438 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a286) (via sym1 fix1 (by decide +kernel) (b2_248 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a287) (via sym4 fix4 (by decide +kernel) (b2_250 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_455) (b2_455 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_439,s2_137,a288,a289]) (hints := [773,773,33800,0,36886,33669,37398,3,33541,33669,33800,1,773,773,37398,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_439,s2_137,a288,a289], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_439) (b2_439 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_137) (b2_137 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a288) (via sym7 fix7 (by decide +kernel) (b2_179 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a289) (via sym1 fix1 (by decide +kernel) (b2_459 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a290,a291,a292,s2_446]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a290,a291,a292,s2_446], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a290) (via sym2 fix2 (by decide +kernel) (b2_398 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a291) (via sym2 fix2 (by decide +kernel) (b2_303 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a292) (via sym4 fix4 (by decide +kernel) (b2_303 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_446) (b2_446 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a293,s2_329,a294,s2_450]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a293,s2_329,a294,s2_450], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a293) (via sym3 fix3 (by decide +kernel) (b2_390 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_329) (b2_329 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a294) (via sym5 fix5 (by decide +kernel) (b2_332 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_450) (b2_450 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a295,a296,a297,a298]) (hints := [8453,1542,8453,0,8457,9766,9481,3,8453,9766,8453,1,9477,1542,9481,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a295,a296,a297,a298], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a295) (via sym3 fix3 (by decide +kernel) (b2_411 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a296) (via sym2 fix2 (by decide +kernel) (b2_54 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a297) (via sym4 fix4 (by decide +kernel) (b2_317 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a298) (via sym1 fix1 (by decide +kernel) (b2_445 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a299,a300,a301,s2_456]) (hints := [1542,1542,16902,0,18448,50372,19472,3,16902,50372,16902,1,1542,1542,19472,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a299,a300,a301,s2_456], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a299) (via sym2 fix2 (by decide +kernel) (b2_410 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a300) (via sym3 fix3 (by decide +kernel) (b2_55 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a301) (via sym5 fix5 (by decide +kernel) (b2_318 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_456) (b2_456 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a302,s2_207,a303,a304]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a302,s2_207,a303,a304], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a302) (via sym3 fix3 (by decide +kernel) (b2_375 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_207) (b2_207 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a303) (via sym4 fix4 (by decide +kernel) (b2_347 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a304) (via sym1 fix1 (by decide +kernel) (b2_457 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a305,a306,a307,a308]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a305,a306,a307,a308], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a305) (via sym5 fix5 (by decide +kernel) (b2_390 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a306) (via sym1 fix1 (by decide +kernel) (b2_329 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a307) (via sym3 fix3 (by decide +kernel) (b2_332 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a308) (via sym1 fix1 (by decide +kernel) (b2_450 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a309,a310,a311,a312]) (hints := [8453,18500,8453,0,10252,10276,10252,3,10244,10276,8453,1,10244,18500,10252,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a309,a310,a311,a312], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a309) (via sym4 fix4 (by decide +kernel) (b2_374 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a310) (via sym6 fix6 (by decide +kernel) (b2_213 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a311) (via sym3 fix3 (by decide +kernel) (b2_348 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a312) (via sym1 fix1 (by decide +kernel) (b2_444 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a313,a314,a315,s2_457]) (hints := [16902,10276,16902,0,18444,18500,18444,3,18436,18500,16902,1,18436,10276,18444,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a313,a314,a315,s2_457], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a313) (via sym5 fix5 (by decide +kernel) (b2_375 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a314) (via sym1 fix1 (by decide +kernel) (b2_207 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a315) (via sym2 fix2 (by decide +kernel) (b2_347 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_457) (b2_457 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a316,a317,a318,a319]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a316,a317,a318,a319], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a316) (via sym4 fix4 (by decide +kernel) (b2_410 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a317) (via sym5 fix5 (by decide +kernel) (b2_55 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a318) (via sym3 fix3 (by decide +kernel) (b2_318 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a319) (via sym1 fix1 (by decide +kernel) (b2_456 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a320,a321,a322,a323]) (hints := [8453,20548,8453,0,8469,28772,12565,3,8453,28772,8453,1,12549,20548,12565,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a320,a321,a322,a323], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a320) (via sym7 fix7 (by decide +kernel) (b2_414 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a321) (via sym6 fix6 (by decide +kernel) (b2_58 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a322) (via sym1 fix1 (by decide +kernel) (b2_315 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a323) (via sym1 fix1 (by decide +kernel) (b2_449 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a324,a325,s2_345,s2_458]) (hints := [16902,36996,16902,0,20500,20548,20500,3,20484,20548,16902,1,20484,36996,20500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a324,a325,s2_345,s2_458], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a324) (via sym6 fix6 (by decide +kernel) (b2_378 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a325) (via sym3 fix3 (by decide +kernel) (b2_210 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_345) (b2_345 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_458) (b2_458 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a326,a327,a328,a329]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a326,a327,a328,a329], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a326) (via sym7 fix7 (by decide +kernel) (b2_378 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a327) (via sym5 fix5 (by decide +kernel) (b2_210 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a328) (via sym1 fix1 (by decide +kernel) (b2_345 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a329) (via sym1 fix1 (by decide +kernel) (b2_458 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a330,a331,a332,s2_459]) (hints := [8453,8453,16902,0,25126,24901,25126,3,24837,24901,16902,1,8453,8453,25126,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a330,a331,a332,s2_459], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a330) (via sym1 fix1 (by decide +kernel) (b2_439 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a331) (via sym1 fix1 (by decide +kernel) (b2_137 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a332) (via sym6 fix6 (by decide +kernel) (b2_179 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_459) (b2_459 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_12_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a333,s2_248,a334,a335]) (hints := [8453,8453,33800,0,40996,41092,40996,3,40964,41092,33800,1,40964,8453,40996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a333,s2_248,a334,a335], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a333) (via sym1 fix1 (by decide +kernel) (b2_438 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_248) (b2_248 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a334) (via sym2 fix2 (by decide +kernel) (b2_250 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a335) (via sym1 fix1 (by decide +kernel) (b2_455 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_12_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_12 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_452,a336,a337,s2_461]) (hints := [16902,16902,33800,0,33864,49798,50248,3,49670,49798,33800,1,16902,16902,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_452,a336,a337,s2_461], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_452) (b2_452 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a336) (via sym5 fix5 (by decide +kernel) (b2_170 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a337) (via sym3 fix3 (by decide +kernel) (b2_170 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_461) (b2_461 theta) <|
    PetersenLocalChildren.nil
theorem b1_12 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_12 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 10 s1_12 pair
  exact PetersenLocalChildren.push (pair1_12_0 theta) <|
    PetersenLocalChildren.push (pair1_12_1 theta) <|
    PetersenLocalChildren.push (pair1_12_2 theta) <|
    PetersenLocalChildren.push (pair1_12_3 theta) <|
    PetersenLocalChildren.push (pair1_12_4 theta) <|
    PetersenLocalChildren.push (pair1_12_5 theta) <|
    PetersenLocalChildren.push (pair1_12_6 theta) <|
    PetersenLocalChildren.push (pair1_12_7 theta) <|
    PetersenLocalChildren.push (pair1_12_8 theta) <|
    PetersenLocalChildren.push (pair1_12_9 theta) <|
    PetersenLocalChildren.push (pair1_12_10 theta) <|
    PetersenLocalChildren.push (pair1_12_11 theta) <|
    PetersenLocalChildren.push (pair1_12_12 theta) <|
    PetersenLocalChildren.push (pair1_12_13 theta) <|
    PetersenLocalChildren.push (pair1_12_14 theta) <|
    PetersenLocalChildren.push (pair1_12_15 theta) <|
    PetersenLocalChildren.push (pair1_12_16 theta) <|
    PetersenLocalChildren.push (pair1_12_17 theta) <|
    PetersenLocalChildren.push (pair1_12_18 theta) <|
    PetersenLocalChildren.push (pair1_12_19 theta) <|
    PetersenLocalChildren.push (pair1_12_20 theta) <|
    PetersenLocalChildren.push (pair1_12_21 theta) <|
    PetersenLocalChildren.push (pair1_12_22 theta) <|
    PetersenLocalChildren.push (pair1_12_23 theta) <|
    PetersenLocalChildren.push (pair1_12_24 theta) <|
    PetersenLocalChildren.push (pair1_12_25 theta) <|
    PetersenLocalChildren.push (pair1_12_26 theta) <|
    PetersenLocalChildren.push (pair1_12_27 theta) <|
    PetersenLocalChildren.push (pair1_12_28 theta) <|
    PetersenLocalChildren.push (pair1_12_29 theta) <|
    PetersenLocalChildren.push (pair1_12_30 theta) <|
    PetersenLocalChildren.push (pair1_12_31 theta) <|
    PetersenLocalChildren.push (pair1_12_32 theta) <|
    PetersenLocalChildren.push (pair1_12_33 theta) <|
    PetersenLocalChildren.push (pair1_12_34 theta) <|
    PetersenLocalChildren.push (pair1_12_35 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
