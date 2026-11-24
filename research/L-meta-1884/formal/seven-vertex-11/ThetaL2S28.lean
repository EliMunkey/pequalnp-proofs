import ThetaAlias
import ThetaL3S0
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S10
import ThetaL3S11
import ThetaL3S25
import ThetaL3S31
import ThetaL3S32
import ThetaL3S35
import ThetaL3S36
import ThetaL3S39
import ThetaL3S42
import ThetaL3S43
import ThetaL3S46
import ThetaL3S47
import ThetaL3S48
import ThetaL3S49
import ThetaL3S50
import ThetaL3S58
import ThetaL3S59
import ThetaL3S60
import ThetaL3S71
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_672 : Blocked tgt 8 s2_672 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_672 8 _ le
  decide +kernel
theorem b2_673 : Blocked tgt 8 s2_673 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s2_673 8 _ le
  decide +kernel
theorem b2_674 : Blocked tgt 8 s2_674 := by
  apply node_sound (nxt := [s3_1048,a1406,s3_1192,s3_1406,s3_3,s3_1767,s3_1161,a1407,s3_752,a1408,a1409,s3_1130,a1410,s3_1431,s3_1711,a1411,a1412,a1413,a1414,a1415,a1416,a1417,a1418,a1419,s3_114,a1420,a1421,a1422,s3_1159,s3_790,s3_1164,s3_1157,a1423,a1424,s3_1160,s3_261,s3_1162])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1048
    · exact via sym2 fix2 (by decide +kernel) b3_753
    · exact b3_1192
    · exact b3_1406
    · exact b3_3
    · exact b3_1767
    · exact b3_1161
    · exact via sym2 fix2 (by decide +kernel) b3_1028
    · exact b3_752
    · exact via sym3 fix3 (by decide +kernel) b3_1219
    · exact via sym2 fix2 (by decide +kernel) b3_1409
    · exact b3_1130
    · exact via sym1 fix1 (by decide +kernel) b3_95
    · exact b3_1431
    · exact b3_1711
    · exact via sym2 fix2 (by decide +kernel) b3_1119
    · exact via sym3 fix3 (by decide +kernel) b3_123
    · exact via sym2 fix2 (by decide +kernel) b3_1454
    · exact via sym2 fix2 (by decide +kernel) b3_1715
    · exact via sym3 fix3 (by decide +kernel) b3_1123
    · exact via sym2 fix2 (by decide +kernel) b3_120
    · exact via sym3 fix3 (by decide +kernel) b3_1450
    · exact via sym3 fix3 (by decide +kernel) b3_1718
    · exact via sym1 fix1 (by decide +kernel) b3_1127
    · exact b3_114
    · exact via sym1 fix1 (by decide +kernel) b3_1442
    · exact via sym1 fix1 (by decide +kernel) b3_1721
    · exact via sym2 fix2 (by decide +kernel) b3_846
    · exact b3_1159
    · exact b3_790
    · exact b3_1164
    · exact b3_1157
    · exact via sym2 fix2 (by decide +kernel) b3_1041
    · exact via sym1 fix1 (by decide +kernel) b3_264
    · exact b3_1160
    · exact b3_261
    · exact b3_1162
theorem b2_675 : Blocked tgt 8 s2_675 := by
  intro m le c
  apply rejects_sound extra54 i5 4 tgt small54 hot54 [] s2_675 8 _ le
  decide +kernel
theorem b2_676 : Blocked tgt 8 s2_676 := by
  apply node_sound (nxt := [s3_1025,a1425,a1426,s3_1407,s3_3,s3_1779,s3_1169,a1302,s3_750,a1120,a1427,s3_1130,a1428,s3_1431,s3_1712,a1429,a1430,a1431,a1432,a1433,a1434,a1435,a1436,a1437,s3_115,a1438,a1439,s3_1165,s3_1040,s3_845,s3_1167,a1440,s3_1168,a1441,s3_1170,a1442,s3_1171])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1025
    · exact via sym2 fix2 (by decide +kernel) b3_754
    · exact via sym1 fix1 (by decide +kernel) b3_1210
    · exact b3_1407
    · exact b3_3
    · exact b3_1779
    · exact b3_1169
    · exact via sym2 fix2 (by decide +kernel) b3_1048
    · exact b3_750
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact via sym2 fix2 (by decide +kernel) b3_1408
    · exact b3_1130
    · exact via sym1 fix1 (by decide +kernel) b3_101
    · exact b3_1431
    · exact b3_1712
    · exact via sym2 fix2 (by decide +kernel) b3_1118
    · exact via sym3 fix3 (by decide +kernel) b3_121
    · exact via sym2 fix2 (by decide +kernel) b3_1455
    · exact via sym2 fix2 (by decide +kernel) b3_1714
    · exact via sym3 fix3 (by decide +kernel) b3_1122
    · exact via sym2 fix2 (by decide +kernel) b3_119
    · exact via sym3 fix3 (by decide +kernel) b3_1451
    · exact via sym3 fix3 (by decide +kernel) b3_1717
    · exact via sym1 fix1 (by decide +kernel) b3_1128
    · exact b3_115
    · exact via sym1 fix1 (by decide +kernel) b3_1441
    · exact via sym1 fix1 (by decide +kernel) b3_1722
    · exact b3_1165
    · exact b3_1040
    · exact b3_845
    · exact b3_1167
    · exact via sym1 fix1 (by decide +kernel) b3_265
    · exact b3_1168
    · exact via sym3 fix3 (by decide +kernel) b3_263
    · exact b3_1170
    · exact via sym2 fix2 (by decide +kernel) b3_262
    · exact b3_1171
theorem b2_677 : Blocked tgt 8 s2_677 := by
  intro m le c
  apply rejects_sound extra70 i5 4 tgt small70 hot70 [] s2_677 8 _ le
  decide +kernel
theorem b2_678 : Blocked tgt 8 s2_678 := by
  apply node_sound (nxt := [s3_1029,a1443,a1444,s3_1410,s3_3,s3_1796,s3_1180,a1445,s3_755,a1446,a1447,s3_1130,a1448,s3_1431,s3_1716,a1449,a1450,a1451,a1452,a1453,a1454,a1455,a1456,a1457,s3_124,a1458,a1459,a1460,a1461,a1462,s3_1179,a1463,a1464,a1465,s3_1178])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1029
    · exact via sym3 fix3 (by decide +kernel) b3_755
    · exact via sym1 fix1 (by decide +kernel) b3_1205
    · exact b3_1410
    · exact b3_3
    · exact b3_1796
    · exact b3_1180
    · exact via sym3 fix3 (by decide +kernel) b3_1029
    · exact b3_755
    · exact via sym2 fix2 (by decide +kernel) b3_1205
    · exact via sym3 fix3 (by decide +kernel) b3_1410
    · exact b3_1130
    · exact via sym1 fix1 (by decide +kernel) b3_116
    · exact b3_1431
    · exact b3_1716
    · exact via sym2 fix2 (by decide +kernel) b3_1129
    · exact via sym3 fix3 (by decide +kernel) b3_124
    · exact via sym2 fix2 (by decide +kernel) b3_1436
    · exact via sym2 fix2 (by decide +kernel) b3_1723
    · exact via sym3 fix3 (by decide +kernel) b3_1130
    · exact via sym2 fix2 (by decide +kernel) b3_116
    · exact via sym3 fix3 (by decide +kernel) b3_1431
    · exact via sym3 fix3 (by decide +kernel) b3_1716
    · exact via sym1 fix1 (by decide +kernel) b3_1129
    · exact b3_124
    · exact via sym1 fix1 (by decide +kernel) b3_1436
    · exact via sym1 fix1 (by decide +kernel) b3_1723
    · exact via sym2 fix2 (by decide +kernel) b3_938
    · exact via sym3 fix3 (by decide +kernel) b3_1178
    · exact via sym1 fix1 (by decide +kernel) b3_267
    · exact b3_1179
    · exact via sym2 fix2 (by decide +kernel) b3_267
    · exact via sym3 fix3 (by decide +kernel) b3_1179
    · exact via sym1 fix1 (by decide +kernel) b3_938
    · exact b3_1178
theorem b2_679 : Blocked tgt 8 s2_679 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s2_679 8 _ le
  decide +kernel
theorem b2_680 : Blocked tgt 8 s2_680 := by
  apply node_sound (nxt := [s3_1030,a1466,s3_1217,s3_1411,s3_3,s3_1808,s3_1187,a1467,s3_756,a1468,a1469,s3_1124,a1470,s3_1445,s3_1719,a1471,a1472,a1473,a1474,a1453,a1475,a1455,a1476,a1477,s3_125,a1478,a1479,a1480,a1481,a1482,s3_1184,a1483,s3_1186,a1484,a1485,s3_937,a1486,a1487,s3_1185,s3_1182,a1488,a1489,a1490])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1030
    · exact via sym2 fix2 (by decide +kernel) b3_757
    · exact b3_1217
    · exact b3_1411
    · exact b3_3
    · exact b3_1808
    · exact b3_1187
    · exact via sym2 fix2 (by decide +kernel) b3_1031
    · exact b3_756
    · exact via sym2 fix2 (by decide +kernel) b3_1207
    · exact via sym2 fix2 (by decide +kernel) b3_1412
    · exact b3_1124
    · exact via sym1 fix1 (by decide +kernel) b3_125
    · exact b3_1445
    · exact b3_1719
    · exact via sym2 fix2 (by decide +kernel) b3_1130
    · exact via sym3 fix3 (by decide +kernel) b3_111
    · exact via sym2 fix2 (by decide +kernel) b3_1431
    · exact via sym2 fix2 (by decide +kernel) b3_1720
    · exact via sym3 fix3 (by decide +kernel) b3_1130
    · exact via sym2 fix2 (by decide +kernel) b3_111
    · exact via sym3 fix3 (by decide +kernel) b3_1431
    · exact via sym3 fix3 (by decide +kernel) b3_1720
    · exact via sym1 fix1 (by decide +kernel) b3_1124
    · exact b3_125
    · exact via sym1 fix1 (by decide +kernel) b3_1445
    · exact via sym1 fix1 (by decide +kernel) b3_1719
    · exact via sym2 fix2 (by decide +kernel) b3_883
    · exact via sym1 fix1 (by decide +kernel) b3_1184
    · exact via sym3 fix3 (by decide +kernel) b3_883
    · exact b3_1184
    · exact via sym3 fix3 (by decide +kernel) b3_266
    · exact b3_1186
    · exact via sym2 fix2 (by decide +kernel) b3_266
    · exact via sym1 fix1 (by decide +kernel) b3_1186
    · exact b3_937
    · exact via sym1 fix1 (by decide +kernel) b3_1185
    · exact via sym1 fix1 (by decide +kernel) b3_937
    · exact b3_1185
    · exact b3_1182
    · exact via sym3 fix3 (by decide +kernel) b3_602
    · exact via sym1 fix1 (by decide +kernel) b3_1182
    · exact via sym2 fix2 (by decide +kernel) b3_602
theorem b2_681 : Blocked tgt 8 s2_681 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_681 8 _ le
  decide +kernel
theorem b2_682 : Blocked tgt 8 s2_682 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_682 8 _ le
  decide +kernel
theorem b2_683 : Blocked tgt 8 s2_683 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,false))] s2_683 8 _ le
  decide +kernel
theorem b2_684 : Blocked tgt 8 s2_684 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_684 8 _ le
  decide +kernel
theorem b2_685 : Blocked tgt 8 s2_685 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_685 8 _ le
  decide +kernel
theorem b2_686 : Blocked tgt 8 s2_686 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_686 8 _ le
  decide +kernel
theorem b2_687 : Blocked tgt 8 s2_687 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_687 8 _ le
  decide +kernel
theorem b2_688 : Blocked tgt 8 s2_688 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_688 8 _ le
  decide +kernel
theorem b2_689 : Blocked tgt 8 s2_689 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_689 8 _ le
  decide +kernel
theorem b2_690 : Blocked tgt 8 s2_690 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_690 8 _ le
  decide +kernel
theorem b2_691 : Blocked tgt 8 s2_691 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_691 8 _ le
  decide +kernel
theorem b2_692 : Blocked tgt 8 s2_692 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_692 8 _ le
  decide +kernel
theorem b2_693 : Blocked tgt 8 s2_693 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s2_693 8 _ le
  decide +kernel
theorem b2_694 : Blocked tgt 8 s2_694 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_694 8 _ le
  decide +kernel
theorem b2_695 : Blocked tgt 8 s2_695 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_695 8 _ le
  decide +kernel
end ThetaCert
