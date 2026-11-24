import ThetaAlias
import ThetaL3S4
import ThetaL3S8
import ThetaL3S14
import ThetaL3S18
import ThetaL3S22
import ThetaL3S25
import ThetaL3S30
import ThetaL3S32
import ThetaL3S36
import ThetaL3S39
import ThetaL3S43
import ThetaL3S45
import ThetaL3S46
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_648 : Blocked tgt 8 s2_648 := by
  apply node_sound (nxt := [s3_1038,a1353,s3_1088,s3_1093,a1249,s3_740,a1317,a1354,s3_1085,a1355,s3_1097,s3_1105,a1356,a1357,a1358,a1359,a1360,a1361,a1362,a1363,a1364,s3_109,a1365,a1366,s3_1089,s3_787,a1334,s3_1100,s3_1091,a1367,a1368,s3_1106,s3_1092,a1369,a1370,a1371,a1372,a1373,a1374,a1375,a1376,s3_192,a1377,a1378,a1379,a1380,s3_882,s3_1108,a1381,a1382,s3_936,a1383,a1384,a1385,a1386,a1387,a1388,s3_350,a1389,a1390,s3_1102,a1391,a1392,s3_1110,s3_1103,a1393,a1394,s3_1111,s3_1104,s3_442,a1395,a1396,a1397,a1398,a1399,s3_1112,a1400,s3_534,a1401,a1402,a1403,s3_601,a1404,a1405])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1038
    · exact via sym2 fix2 (by decide +kernel) b3_740
    · exact b3_1088
    · exact b3_1093
    · exact via sym2 fix2 (by decide +kernel) b3_1038
    · exact b3_740
    · exact via sym2 fix2 (by decide +kernel) b3_1088
    · exact via sym2 fix2 (by decide +kernel) b3_1093
    · exact b3_1085
    · exact via sym1 fix1 (by decide +kernel) b3_109
    · exact b3_1097
    · exact b3_1105
    · exact via sym2 fix2 (by decide +kernel) b3_1085
    · exact via sym3 fix3 (by decide +kernel) b3_109
    · exact via sym2 fix2 (by decide +kernel) b3_1097
    · exact via sym2 fix2 (by decide +kernel) b3_1105
    · exact via sym3 fix3 (by decide +kernel) b3_1085
    · exact via sym2 fix2 (by decide +kernel) b3_109
    · exact via sym3 fix3 (by decide +kernel) b3_1097
    · exact via sym3 fix3 (by decide +kernel) b3_1105
    · exact via sym1 fix1 (by decide +kernel) b3_1085
    · exact b3_109
    · exact via sym1 fix1 (by decide +kernel) b3_1097
    · exact via sym1 fix1 (by decide +kernel) b3_1105
    · exact b3_1089
    · exact b3_787
    · exact via sym2 fix2 (by decide +kernel) b3_787
    · exact b3_1100
    · exact b3_1091
    · exact via sym1 fix1 (by decide +kernel) b3_192
    · exact via sym2 fix2 (by decide +kernel) b3_936
    · exact b3_1106
    · exact b3_1092
    · exact via sym3 fix3 (by decide +kernel) b3_350
    · exact via sym2 fix2 (by decide +kernel) b3_882
    · exact via sym2 fix2 (by decide +kernel) b3_1108
    · exact via sym1 fix1 (by decide +kernel) b3_1092
    · exact via sym2 fix2 (by decide +kernel) b3_350
    · exact via sym3 fix3 (by decide +kernel) b3_882
    · exact via sym3 fix3 (by decide +kernel) b3_1108
    · exact via sym1 fix1 (by decide +kernel) b3_1091
    · exact b3_192
    · exact via sym3 fix3 (by decide +kernel) b3_936
    · exact via sym1 fix1 (by decide +kernel) b3_1106
    · exact via sym2 fix2 (by decide +kernel) b3_1092
    · exact via sym1 fix1 (by decide +kernel) b3_350
    · exact b3_882
    · exact b3_1108
    · exact via sym2 fix2 (by decide +kernel) b3_1091
    · exact via sym3 fix3 (by decide +kernel) b3_192
    · exact b3_936
    · exact via sym2 fix2 (by decide +kernel) b3_1106
    · exact via sym3 fix3 (by decide +kernel) b3_1091
    · exact via sym2 fix2 (by decide +kernel) b3_192
    · exact via sym1 fix1 (by decide +kernel) b3_936
    · exact via sym3 fix3 (by decide +kernel) b3_1106
    · exact via sym3 fix3 (by decide +kernel) b3_1092
    · exact b3_350
    · exact via sym1 fix1 (by decide +kernel) b3_882
    · exact via sym1 fix1 (by decide +kernel) b3_1108
    · exact b3_1102
    · exact via sym3 fix3 (by decide +kernel) b3_601
    · exact via sym1 fix1 (by decide +kernel) b3_601
    · exact b3_1110
    · exact b3_1103
    · exact via sym2 fix2 (by decide +kernel) b3_534
    · exact via sym1 fix1 (by decide +kernel) b3_534
    · exact b3_1111
    · exact b3_1104
    · exact b3_442
    · exact via sym1 fix1 (by decide +kernel) b3_442
    · exact via sym2 fix2 (by decide +kernel) b3_1112
    · exact via sym2 fix2 (by decide +kernel) b3_1104
    · exact via sym2 fix2 (by decide +kernel) b3_442
    · exact via sym3 fix3 (by decide +kernel) b3_442
    · exact b3_1112
    · exact via sym1 fix1 (by decide +kernel) b3_1103
    · exact b3_534
    · exact via sym3 fix3 (by decide +kernel) b3_534
    · exact via sym1 fix1 (by decide +kernel) b3_1111
    · exact via sym1 fix1 (by decide +kernel) b3_1102
    · exact b3_601
    · exact via sym2 fix2 (by decide +kernel) b3_601
    · exact via sym1 fix1 (by decide +kernel) b3_1110
theorem b2_649 : Blocked tgt 8 s2_649 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,false))] s2_649 8 _ le
  decide +kernel
theorem b2_650 : Blocked tgt 8 s2_650 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_650 8 _ le
  decide +kernel
theorem b2_651 : Blocked tgt 8 s2_651 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_651 8 _ le
  decide +kernel
theorem b2_652 : Blocked tgt 8 s2_652 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_652 8 _ le
  decide +kernel
theorem b2_653 : Blocked tgt 8 s2_653 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_653 8 _ le
  decide +kernel
theorem b2_654 : Blocked tgt 8 s2_654 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_654 8 _ le
  decide +kernel
theorem b2_655 : Blocked tgt 8 s2_655 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_655 8 _ le
  decide +kernel
theorem b2_656 : Blocked tgt 8 s2_656 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_656 8 _ le
  decide +kernel
theorem b2_657 : Blocked tgt 8 s2_657 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_657 8 _ le
  decide +kernel
theorem b2_658 : Blocked tgt 8 s2_658 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_658 8 _ le
  decide +kernel
theorem b2_659 : Blocked tgt 8 s2_659 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s2_659 8 _ le
  decide +kernel
theorem b2_660 : Blocked tgt 8 s2_660 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s2_660 8 _ le
  decide +kernel
theorem b2_661 : Blocked tgt 8 s2_661 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s2_661 8 _ le
  decide +kernel
theorem b2_662 : Blocked tgt 8 s2_662 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_662 8 _ le
  decide +kernel
theorem b2_663 : Blocked tgt 8 s2_663 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_663 8 _ le
  decide +kernel
theorem b2_664 : Blocked tgt 8 s2_664 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_664 8 _ le
  decide +kernel
theorem b2_665 : Blocked tgt 8 s2_665 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s2_665 8 _ le
  decide +kernel
theorem b2_666 : Blocked tgt 8 s2_666 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s2_666 8 _ le
  decide +kernel
theorem b2_667 : Blocked tgt 8 s2_667 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s2_667 8 _ le
  decide +kernel
theorem b2_668 : Blocked tgt 8 s2_668 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_668 8 _ le
  decide +kernel
theorem b2_669 : Blocked tgt 8 s2_669 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_669 8 _ le
  decide +kernel
theorem b2_670 : Blocked tgt 8 s2_670 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_670 8 _ le
  decide +kernel
theorem b2_671 : Blocked tgt 8 s2_671 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_671 8 _ le
  decide +kernel
end ThetaCert
