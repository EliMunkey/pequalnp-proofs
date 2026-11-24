import PetersenLocalChildren
import Q1020K12L2S6Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S14
import Q1020K12L3S15
import Q1020K12L3S16
import Q1020K12L3S17
import Q1020K12L3S19
import Q1020K12L3S22
import Q1020K12L3S26
import Q1020K12L3S27
import Q1020K12L3S30
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S35
import Q1020K12L3S36
import Q1020K12L3S37
import Q1020K12L3S38
import Q1020K12L3S57
import Q1020K12L3S62
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S71
import Q1020K12L3S73
import Q1020K12L3S78
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S6Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
private theorem pair2_279_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_407,a1317,a1318,s3_2724]) (hints := [33670,0,33670,774,3,774,33670,1,33670,774,2,774]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_407,a1317,a1318,s3_2724], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_407) (b3_407 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1317) (via sym5 fix5 (by decide +kernel) (b3_367 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1318) (via sym1 fix1 (by decide +kernel) (b3_2624 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2724) (b3_2724 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1124,s3_944,s3_644,a1319,a1320,a1321,a1322,s3_3009]) (hints := [0,1,2,9772,7,9772,3,4,5,9772,6,9772]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1124,s3_944,s3_644,a1319,a1320,a1321,a1322,s3_3009], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1124) (b3_1124 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_944) (b3_944 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_644) (b3_644 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1319) (via sym4 fix4 (by decide +kernel) (b3_144 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1320) (via sym4 fix4 (by decide +kernel) (b3_132 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1321) (via sym4 fix4 (by decide +kernel) (b3_85 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1322) (via sym3 fix3 (by decide +kernel) (b3_2800 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3009) (b3_3009 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1161,a1323,a1324,a1325]) (hints := [33924,0,33924,1542,3,1542,33924,1,33924,1542,2,1542]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1161,a1323,a1324,a1325], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1161) (b3_1161 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1323) (via sym5 fix5 (by decide +kernel) (b3_326 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1324) (via sym3 fix3 (by decide +kernel) (b3_2425 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1325) (via sym2 fix2 (by decide +kernel) (b3_2751 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1326,s3_349,a1327,a1328]) (hints := [18500,0,18500,10276,3,10276,18500,1,18500,10276,2,10276]) (by decide +kernel) ?_
  change ∀ V ∈ [a1326,s3_349,a1327,a1328], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1326) (via sym5 fix5 (by decide +kernel) (b3_426 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_349) (b3_349 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1327) (via sym4 fix4 (by decide +kernel) (b3_2615 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1328) (via sym5 fix5 (by decide +kernel) (b3_2733 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1329,s3_308,a1330,a1331]) (hints := [20548,0,20548,28772,3,28772,20548,1,20548,28772,2,28772]) (by decide +kernel) ?_
  change ∀ V ∈ [a1329,s3_308,a1330,a1331], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1329) (via sym5 fix5 (by decide +kernel) (b3_1167 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_308) (b3_308 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1330) (via sym7 fix7 (by decide +kernel) (b3_2408 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1331) (via sym6 fix6 (by decide +kernel) (b3_2753 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1402,s3_260,a1332,a1333]) (hints := [41606,0,41606,10766,3,10766,41606,1,41606,10766,2,10766]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1402,s3_260,a1332,a1333], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1402) (b3_1402 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_260) (b3_260 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1332) (via sym1 fix1 (by decide +kernel) (b3_2883 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1333) (via sym1 fix1 (by decide +kernel) (b3_3085 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_21,s3_18,s3_5,a1334,a1335,s3_1564]) (hints := [0,1,2,3,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_21,s3_18,s3_5,a1334,a1335,s3_1564], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_21) (b3_21 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_18) (b3_18 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_5) (b3_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1334) (via sym3 fix3 (by decide +kernel) (b3_2942 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1335) (via sym3 fix3 (by decide +kernel) (b3_2936 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1564) (b3_1564 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1336,s3_196,a1337,a1338]) (hints := [18444,0,18444,16902,3,16902,18444,1,18444,16902,2,16902]) (by decide +kernel) ?_
  change ∀ V ∈ [a1336,s3_196,a1337,a1338], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1336) (via sym5 fix5 (by decide +kernel) (b3_612 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_196) (b3_196 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1337) (via sym6 fix6 (by decide +kernel) (b3_2839 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1338) (via sym5 fix5 (by decide +kernel) (b3_3068 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_18,a1339,s3_1568]) (hints := [33799,0,33799,37397,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_18,a1339,s3_1568], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_18) (b3_18 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1339) (via sym1 fix1 (by decide +kernel) (b3_3281 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1568) (b3_1568 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1496,s3_1604]) (hints := [8482,8482,9766,772,772,1,772,772,9766,8482,8482,0]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1496,s3_1604], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1496) (b3_1496 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1604) (b3_1604 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,1538,8484,9508,34177,1538,9508,1538,770,770,34177]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10272,778,2826,18753,2818,2826,10272,770,770,18753]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,20544,786,4882,20801,4866,4882,20544,770,770,20801]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1501,s3_1600]) (hints := [772,772,10764,8482,8482,1,8964,8482,10764,772,772,0]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1501,s3_1600], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1501) (b3_1501 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1600) (b3_1600 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1514,s3_1513,s3_1512,a1340,s3_1504,s3_1503,s3_1502,s3_1569]) (hints := [0,1,2,778,778,7,778,778,3,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1514,s3_1513,s3_1512,a1340,s3_1504,s3_1503,s3_1502,s3_1569], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1514) (b3_1514 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1513) (b3_1513 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1512) (b3_1512 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1340) (via sym6 fix6 (by decide +kernel) (b3_185 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1504) (b3_1504 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1503) (b3_1503 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1502) (b3_1502 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1569) (b3_1569 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,16898,18441,24928,18697,16898,24928,16898,770,770,18697]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,33796,33797,33666,34053,33796,33666,33796,770,770,34053]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [25184,25184,33920,1538,9764,1538,9760,9764,33920,1538,25184,1538]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1478,s3_1605]) (hints := [10274,9766,10274,10276,1,10788,10274,0,10274,10786,9766,10788]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1478,s3_1605], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1478) (b3_1478 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1605) (b3_1605 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [9764,9764,20544,9780,13876,37506,13860,13876,20544,9764,9764,37506]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1524,s3_1523,a1341,a1342]) (hints := [10254,0,1,9768,9768,2,10766,3,10766]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1524,s3_1523,a1341,a1342], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1524) (b3_1524 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1523) (b3_1523 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1341) (via sym2 fix2 (by decide +kernel) (b3_724 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1342) (via sym4 fix4 (by decide +kernel) (b3_687 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_5,a1342,a1343]) (hints := [9767,9767,0,33668,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_5,a1342,a1343], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_5) (b3_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1342) (via sym4 fix4 (by decide +kernel) (b3_687 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1343) (via sym4 fix4 (by decide +kernel) (b3_686 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [18440,9764,18440,16898,25184,16898,18440,25184,18440,16898,9764,16898]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_644,a1344,s3_1607,s3_1606,s3_1566]) (hints := [33801,9769,33801,2,3,4,33801,0,33801,9769,9769,1]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_644,a1344,s3_1607,s3_1606,s3_1566], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_644) (b3_644 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1344) (via sym7 fix7 (by decide +kernel) (b3_804 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1607) (b3_1607 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1606) (b3_1606 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1566) (b3_1566 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,10272,1546,3594,11300,3586,3594,10272,1538,1538,11300]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,20544,1554,5650,21572,5634,5650,20544,1538,1538,21572]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1490,s3_1601]) (hints := [1540,1540,10764,1572,9764,1,9732,9764,10764,1540,1540,0]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1490,s3_1601], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1490) (b3_1490 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1601) (b3_1601 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1532,a1345,s3_1492,s3_1571]) (hints := [33924,33924,0,1542,1542,3,1542,1542,1,33924,33924,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1532,a1345,s3_1492,s3_1571], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1532) (b3_1532 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1345) (via sym7 fix7 (by decide +kernel) (b3_166 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1492) (b3_1492 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1571) (b3_1571 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,16898,18444,50368,19468,16898,50368,16898,1538,1538,19468]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,36880,33796,33920,33796,33792,33920,36880,33792,1538,33796]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10272,10272,20544,10288,14384,39048,14368,14384,20544,10272,10272,39048]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [18496,18496,41602,10762,10272,10762,10754,10272,41602,10754,18496,10762]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1541,a1346,s3_1482,s3_1573]) (hints := [18500,18500,0,10276,10276,3,10276,10276,1,18500,18500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1541,a1346,s3_1482,s3_1573], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1541) (b3_1541 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1346) (via sym6 fix6 (by decide +kernel) (b3_161 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1482) (b3_1482 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1573) (b3_1573 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,10272,16898,18440,18496,18440,18432,18496,16898,18432,10272,18440]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,10272,33796,33804,51392,35852,33796,51392,33796,35844,10272,35852]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10762,20544,10762,10778,28768,14874,10762,28768,10762,14858,20544,14874]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_36 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1550,a1347,s3_1473,s3_1575]) (hints := [20548,20548,0,28772,28772,3,28772,28772,1,20548,20548,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1550,a1347,s3_1473,s3_1575], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1550) (b3_1550 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1347) (via sym6 fix6 (by decide +kernel) (b3_50 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1473) (b3_1473 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1575) (b3_1575 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_37 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,36992,16898,20496,20544,20496,20480,20544,16898,20480,36992,20496]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_38 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,20544,33796,36880,36992,36880,36864,36992,33796,36864,20544,36880]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_279_39 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_5,a1341,a1348]) (hints := [10765,10765,0,41091,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_5,a1341,a1348], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_5) (b3_5 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1341) (via sym2 fix2 (by decide +kernel) (b3_724 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1348) (via sym2 fix2 (by decide +kernel) (b3_723 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_279_40 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1349,s3_1602]) (hints := [16900,10764,16900,16932,1,25124,16900,0,16900,25092,10764,25124]) (by decide +kernel) ?_
  change ∀ V ∈ [a1349,s3_1602], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1349) (via sym1 fix1 (by decide +kernel) (b3_682 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1602) (b3_1602 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_41 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1350,s3_1567]) (hints := [33798,10764,33798,41604,41604,1,33798,41604,33798,10764,10764,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a1350,s3_1567], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1350) (via sym2 fix2 (by decide +kernel) (b3_1293 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1567) (b3_1567 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_42 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1563,s3_1467,a1351,s3_1585]) (hints := [18444,0,18444,16902,3,16902,18444,1,18444,16902,2,16902]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1563,s3_1467,a1351,s3_1585], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1563) (b3_1563 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1467) (b3_1467 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1351) (via sym6 fix6 (by decide +kernel) (b3_90 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1585) (b3_1585 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_43 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1564,s3_1568,a1352,a1353,a1354,s3_1599,s3_1593]) (hints := [33803,0,33803,5,6,1,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1564,s3_1568,a1352,a1353,a1354,s3_1599,s3_1593], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1564) (b3_1564 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1568) (b3_1568 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1352) (via sym7 fix7 (by decide +kernel) (b3_105 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1353) (via sym7 fix7 (by decide +kernel) (b3_104 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1354) (via sym7 fix7 (by decide +kernel) (b3_106 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1599) (b3_1599 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1593) (b3_1593 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_279_44 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_279 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,16898,33796,33860,49794,50244,33796,49794,33796,16898,16898,50244]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
theorem b2_279 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_279 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xffffffffccccccccffffffffcccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa),(0xffffffffccccccccffffffffcccccccc,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xffffffffccccccccffffffffcccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xffffffffccccccccffffffffcccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xffffffffccccccccffffffffcccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xffffffffccccccccffffffffcccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffffffffccccccccffffffffcccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 9 s2_279 pair
  exact PetersenLocalChildren.push (pair2_279_0 theta) <|
    PetersenLocalChildren.push (pair2_279_1 theta) <|
    PetersenLocalChildren.push (pair2_279_2 theta) <|
    PetersenLocalChildren.push (pair2_279_3 theta) <|
    PetersenLocalChildren.push (pair2_279_4 theta) <|
    PetersenLocalChildren.push (pair2_279_5 theta) <|
    PetersenLocalChildren.push (pair2_279_6 theta) <|
    PetersenLocalChildren.push (pair2_279_7 theta) <|
    PetersenLocalChildren.push (pair2_279_8 theta) <|
    PetersenLocalChildren.push (pair2_279_9 theta) <|
    PetersenLocalChildren.push (pair2_279_10 theta) <|
    PetersenLocalChildren.push (pair2_279_11 theta) <|
    PetersenLocalChildren.push (pair2_279_12 theta) <|
    PetersenLocalChildren.push (pair2_279_13 theta) <|
    PetersenLocalChildren.push (pair2_279_14 theta) <|
    PetersenLocalChildren.push (pair2_279_15 theta) <|
    PetersenLocalChildren.push (pair2_279_16 theta) <|
    PetersenLocalChildren.push (pair2_279_17 theta) <|
    PetersenLocalChildren.push (pair2_279_18 theta) <|
    PetersenLocalChildren.push (pair2_279_19 theta) <|
    PetersenLocalChildren.push (pair2_279_20 theta) <|
    PetersenLocalChildren.push (pair2_279_21 theta) <|
    PetersenLocalChildren.push (pair2_279_22 theta) <|
    PetersenLocalChildren.push (pair2_279_23 theta) <|
    PetersenLocalChildren.push (pair2_279_24 theta) <|
    PetersenLocalChildren.push (pair2_279_25 theta) <|
    PetersenLocalChildren.push (pair2_279_26 theta) <|
    PetersenLocalChildren.push (pair2_279_27 theta) <|
    PetersenLocalChildren.push (pair2_279_28 theta) <|
    PetersenLocalChildren.push (pair2_279_29 theta) <|
    PetersenLocalChildren.push (pair2_279_30 theta) <|
    PetersenLocalChildren.push (pair2_279_31 theta) <|
    PetersenLocalChildren.push (pair2_279_32 theta) <|
    PetersenLocalChildren.push (pair2_279_33 theta) <|
    PetersenLocalChildren.push (pair2_279_34 theta) <|
    PetersenLocalChildren.push (pair2_279_35 theta) <|
    PetersenLocalChildren.push (pair2_279_36 theta) <|
    PetersenLocalChildren.push (pair2_279_37 theta) <|
    PetersenLocalChildren.push (pair2_279_38 theta) <|
    PetersenLocalChildren.push (pair2_279_39 theta) <|
    PetersenLocalChildren.push (pair2_279_40 theta) <|
    PetersenLocalChildren.push (pair2_279_41 theta) <|
    PetersenLocalChildren.push (pair2_279_42 theta) <|
    PetersenLocalChildren.push (pair2_279_43 theta) <|
    PetersenLocalChildren.push (pair2_279_44 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
