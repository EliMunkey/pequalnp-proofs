import PetersenLocalChildren
import Q1020K12L2S6Local
import Q1020K12L3S0
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S10
import Q1020K12L3S19
import Q1020K12L3S23
import Q1020K12L3S27
import Q1020K12L3S30
import Q1020K12L3S38
import Q1020K12L3S39
import Q1020K12L3S40
import Q1020K12L3S57
import Q1020K12L3S62
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S72
import Q1020K12L3S74
import Q1020K12L3S79
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S6Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
private theorem pair2_281_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_423,a1402,a1403,s3_2731]) (hints := [8484,0,8484,774,3,774,8484,1,8484,774,2,774]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_423,a1402,a1403,s3_2731], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_423) (b3_423 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1402) (via sym5 fix5 (by decide +kernel) (b3_362 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1403) (via sym1 fix1 (by decide +kernel) (b3_2613 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2731) (b3_2731 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_967,a1404,a1405,s3_3052]) (hints := [49860,0,49860,16964,3,16964,49860,1,49860,16964,2,16964]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_967,a1404,a1405,s3_3052], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_967) (b3_967 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1404) (via sym5 fix5 (by decide +kernel) (b3_127 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1405) (via sym2 fix2 (by decide +kernel) (b3_2796 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3052) (b3_3052 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1164,a1406,a1407,a1408]) (hints := [33924,0,33924,1542,3,1542,33924,1,33924,1542,2,1542]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1164,a1406,a1407,a1408], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1164) (b3_1164 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1406) (via sym5 fix5 (by decide +kernel) (b3_323 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1407) (via sym3 fix3 (by decide +kernel) (b3_2410 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1408) (via sym2 fix2 (by decide +kernel) (b3_2744 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1409,s3_362,a1410,a1411]) (hints := [10276,0,10276,10790,3,10790,10276,1,10276,10790,2,10790]) (by decide +kernel) ?_
  change ∀ V ∈ [a1409,s3_362,a1410,a1411], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1409) (via sym5 fix5 (by decide +kernel) (b3_423 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_362) (b3_362 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1410) (via sym4 fix4 (by decide +kernel) (b3_2613 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1411) (via sym5 fix5 (by decide +kernel) (b3_2731 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1412,s3_323,a1413,a1414]) (hints := [36996,0,36996,20548,3,20548,36996,1,36996,20548,2,20548]) (by decide +kernel) ?_
  change ∀ V ∈ [a1412,s3_323,a1413,a1414], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1412) (via sym5 fix5 (by decide +kernel) (b3_1164 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_323) (b3_323 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1413) (via sym7 fix7 (by decide +kernel) (b3_2410 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1414) (via sym6 fix6 (by decide +kernel) (b3_2744 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1268,s3_286,a1415,a1416]) (hints := [8453,0,8453,10766,3,10766,8453,1,8453,10766,2,10766]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1268,s3_286,a1415,a1416], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1268) (b3_1268 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_286) (b3_286 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1415) (via sym1 fix1 (by decide +kernel) (b3_2912 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1416) (via sym1 fix1 (by decide +kernel) (b3_3108 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1417,s3_127,a1418,a1419]) (hints := [49798,0,49798,16902,3,16902,49798,1,49798,16902,2,16902]) (by decide +kernel) ?_
  change ∀ V ∈ [a1417,s3_127,a1418,a1419], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1417) (via sym5 fix5 (by decide +kernel) (b3_967 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_127) (b3_127 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1418) (via sym6 fix6 (by decide +kernel) (b3_2796 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1419) (via sym5 fix5 (by decide +kernel) (b3_3052 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_21,s3_19,s3_6,a1420,a1421,s3_1666]) (hints := [0,1,2,3,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_21,s3_19,s3_6,a1420,a1421,s3_1666], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_21) (b3_21 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_6) (b3_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1420) (via sym3 fix3 (by decide +kernel) (b3_2975 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1421) (via sym3 fix3 (by decide +kernel) (b3_2976 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1666) (b3_1666 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_19,a1422,s3_1669]) (hints := [33799,0,33799,37397,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_19,a1422,s3_1669], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1422) (via sym2 fix2 (by decide +kernel) (b3_3330 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1669) (b3_1669 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8480,8480,16960,770,770,17217,770,770,16960,8480,8480,17217]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,1538,8484,9508,34177,1538,9508,1538,770,770,34177]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10272,778,2826,18753,2818,2826,10272,770,770,18753]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,20544,786,4882,20801,4866,4882,20544,770,770,20801]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10248,8449,8480,8449,8448,8480,10248,8448,770,8449]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1423,s3_1682]) (hints := [772,772,16900,24930,24930,1,16900,24930,16900,772,772,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a1423,s3_1682], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1423) (via sym5 fix5 (by decide +kernel) (b3_1621 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1682) (b3_1682 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1634,a1424,a1425,s3_1670]) (hints := [8484,8484,0,774,774,3,774,774,1,8484,8484,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1634,a1424,a1425,s3_1670], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1634) (b3_1634 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1424) (via sym1 fix1 (by decide +kernel) (b3_208 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1425) (via sym5 fix5 (by decide +kernel) (b3_1626 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1670) (b3_1670 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,33796,33797,33666,34053,33796,33666,33796,770,770,34053]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16960,16960,33920,1538,17988,1538,17984,17988,33920,1538,16960,1538]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1621,a1426]) (hints := [10274,16962,10274,10788,1,10788,10274,0,10274,10788,16962,10788]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1621,a1426], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1621) (b3_1621 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1426) (via sym5 fix5 (by decide +kernel) (b3_1682 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1611,a1427]) (hints := [16962,16962,20546,37508,1,37508,20546,0,20546,16962,16962,37508]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1611,a1427], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1611) (b3_1611 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1427) (via sym5 fix5 (by decide +kernel) (b3_1683 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,16960,8449,10762,25184,10762,8449,25184,8449,10762,16960,10762]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1428,s3_1642,a1429,a1430]) (hints := [18446,0,1,16964,16964,2,16902,3,16902]) (by decide +kernel) ?_
  change ∀ V ∈ [a1428,s3_1642,a1429,a1430], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1428) (via sym5 fix5 (by decide +kernel) (b3_1642 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1642) (b3_1642 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1429) (via sym1 fix1 (by decide +kernel) (b3_1284 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1430) (via sym4 fix4 (by decide +kernel) (b3_1284 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_6,a1430,a1431]) (hints := [16963,16963,0,33668,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_6,a1430,a1431], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_6) (b3_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1430) (via sym4 fix4 (by decide +kernel) (b3_1284 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1431) (via sym4 fix4 (by decide +kernel) (b3_1283 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1432,s3_1668]) (hints := [33798,16962,33798,49858,49858,1,33798,49858,33798,16962,16962,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a1432,s3_1668], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1432) (via sym7 fix7 (by decide +kernel) (b3_801 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1668) (b3_1668 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,10272,1546,3594,11300,3586,3594,10272,1538,1538,11300]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,20544,1554,5650,21572,5634,5650,20544,1538,1538,21572]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,1538,8449,8453,9762,9477,8449,9762,8449,9473,1538,9477]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1433,s3_1683]) (hints := [1540,1540,16900,50370,50370,1,16900,50370,16900,1540,1540,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a1433,s3_1683], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1433) (via sym5 fix5 (by decide +kernel) (b3_1611 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1683) (b3_1683 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1648,a1434,a1435,s3_1671]) (hints := [33924,33924,0,1542,1542,3,1542,1542,1,33924,33924,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1648,a1434,a1435,s3_1671], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1648) (b3_1648 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1434) (via sym3 fix3 (by decide +kernel) (b3_212 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1435) (via sym5 fix5 (by decide +kernel) (b3_1617 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1671) (b3_1671 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,36880,33796,33920,33796,33792,33920,36880,33792,1538,33796]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10272,10272,20544,10288,14384,39048,14368,14384,20544,10272,10272,39048]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,18496,8449,10248,10272,10248,10240,10272,8449,10240,18496,10248]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,10272,16898,16906,18496,18954,16898,18496,16898,18946,10272,18954]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1436,a1437,s3_1626,a1438]) (hints := [10276,10276,0,10790,10790,3,10790,10790,1,10276,10276,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a1436,a1437,s3_1626,a1438], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1436) (via sym5 fix5 (by decide +kernel) (b3_1634 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1437) (via sym4 fix4 (by decide +kernel) (b3_208 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1626) (b3_1626 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1438) (via sym5 fix5 (by decide +kernel) (b3_1670 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,10272,33796,33804,51392,35852,33796,51392,33796,35844,10272,35852]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,20544,8449,8465,28768,12561,8449,28768,8449,12545,20544,12561]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_36 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,36992,16898,16914,20544,21010,16898,20544,16898,20994,36992,21010]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_37 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1439,a1440,s3_1617,a1441]) (hints := [36996,36996,0,20548,20548,3,20548,20548,1,36996,36996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a1439,a1440,s3_1617,a1441], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1439) (via sym5 fix5 (by decide +kernel) (b3_1648 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1440) (via sym7 fix7 (by decide +kernel) (b3_212 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1617) (b3_1617 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1441) (via sym5 fix5 (by decide +kernel) (b3_1671 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_38 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,20544,33796,36880,36992,36880,36864,36992,33796,36864,20544,36880]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_39 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,8449,16898,16930,24897,25122,16898,24897,16898,8449,8449,25122]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_40 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1659,a1442,s3_1608,s3_1672]) (hints := [8453,8453,0,10766,10766,3,10766,10766,1,8453,8453,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1659,a1442,s3_1608,s3_1672], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1659) (b3_1659 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1442) (via sym1 fix1 (by decide +kernel) (b3_240 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1608) (b3_1608 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1672) (b3_1672 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_281_41 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8449,8449,33796,40992,41088,40992,40960,41088,33796,40960,8449,40992]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_281_42 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_6,a1429,a1443]) (hints := [16901,16901,0,51339,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_6,a1429,a1443], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_6) (b3_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1429) (via sym1 fix1 (by decide +kernel) (b3_1284 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1443) (via sym1 fix1 (by decide +kernel) (b3_1283 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_43 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1444,a1445]) (hints := [16900,16900,33798,49796,49796,1,33798,49796,33798,16900,16900,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a1444,a1445], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1444) (via sym3 fix3 (by decide +kernel) (b3_801 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1445) (via sym5 fix5 (by decide +kernel) (b3_1668 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_281_44 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_281 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1666,s3_1669,a1446,a1447,a1448,s3_1681,s3_1678]) (hints := [33803,0,33803,5,6,1,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1666,s3_1669,a1446,a1447,a1448,s3_1681,s3_1678], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1666) (b3_1666 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1669) (b3_1669 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1446) (via sym3 fix3 (by decide +kernel) (b3_247 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1447) (via sym3 fix3 (by decide +kernel) (b3_246 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1448) (via sym3 fix3 (by decide +kernel) (b3_248 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1681) (b3_1681 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1678) (b3_1678 theta) <|
    PetersenLocalChildren.nil
theorem b2_281 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_281 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xffffffffffffffffcccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa),(0xffffffffffffffffcccccccccccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xffffffffffffffffcccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xffffffffffffffffcccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xffffffffffffffffcccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xffffffffffffffffcccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffffffffffffffffcccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 9 s2_281 pair
  exact PetersenLocalChildren.push (pair2_281_0 theta) <|
    PetersenLocalChildren.push (pair2_281_1 theta) <|
    PetersenLocalChildren.push (pair2_281_2 theta) <|
    PetersenLocalChildren.push (pair2_281_3 theta) <|
    PetersenLocalChildren.push (pair2_281_4 theta) <|
    PetersenLocalChildren.push (pair2_281_5 theta) <|
    PetersenLocalChildren.push (pair2_281_6 theta) <|
    PetersenLocalChildren.push (pair2_281_7 theta) <|
    PetersenLocalChildren.push (pair2_281_8 theta) <|
    PetersenLocalChildren.push (pair2_281_9 theta) <|
    PetersenLocalChildren.push (pair2_281_10 theta) <|
    PetersenLocalChildren.push (pair2_281_11 theta) <|
    PetersenLocalChildren.push (pair2_281_12 theta) <|
    PetersenLocalChildren.push (pair2_281_13 theta) <|
    PetersenLocalChildren.push (pair2_281_14 theta) <|
    PetersenLocalChildren.push (pair2_281_15 theta) <|
    PetersenLocalChildren.push (pair2_281_16 theta) <|
    PetersenLocalChildren.push (pair2_281_17 theta) <|
    PetersenLocalChildren.push (pair2_281_18 theta) <|
    PetersenLocalChildren.push (pair2_281_19 theta) <|
    PetersenLocalChildren.push (pair2_281_20 theta) <|
    PetersenLocalChildren.push (pair2_281_21 theta) <|
    PetersenLocalChildren.push (pair2_281_22 theta) <|
    PetersenLocalChildren.push (pair2_281_23 theta) <|
    PetersenLocalChildren.push (pair2_281_24 theta) <|
    PetersenLocalChildren.push (pair2_281_25 theta) <|
    PetersenLocalChildren.push (pair2_281_26 theta) <|
    PetersenLocalChildren.push (pair2_281_27 theta) <|
    PetersenLocalChildren.push (pair2_281_28 theta) <|
    PetersenLocalChildren.push (pair2_281_29 theta) <|
    PetersenLocalChildren.push (pair2_281_30 theta) <|
    PetersenLocalChildren.push (pair2_281_31 theta) <|
    PetersenLocalChildren.push (pair2_281_32 theta) <|
    PetersenLocalChildren.push (pair2_281_33 theta) <|
    PetersenLocalChildren.push (pair2_281_34 theta) <|
    PetersenLocalChildren.push (pair2_281_35 theta) <|
    PetersenLocalChildren.push (pair2_281_36 theta) <|
    PetersenLocalChildren.push (pair2_281_37 theta) <|
    PetersenLocalChildren.push (pair2_281_38 theta) <|
    PetersenLocalChildren.push (pair2_281_39 theta) <|
    PetersenLocalChildren.push (pair2_281_40 theta) <|
    PetersenLocalChildren.push (pair2_281_41 theta) <|
    PetersenLocalChildren.push (pair2_281_42 theta) <|
    PetersenLocalChildren.push (pair2_281_43 theta) <|
    PetersenLocalChildren.push (pair2_281_44 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
