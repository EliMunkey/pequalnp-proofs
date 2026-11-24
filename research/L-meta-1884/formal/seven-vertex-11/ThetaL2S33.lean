import ThetaAlias
import ThetaL3S0
import ThetaL3S8
import ThetaL3S9
import ThetaL3S11
import ThetaL3S16
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S35
import ThetaL3S43
import ThetaL3S44
import ThetaL3S45
import ThetaL3S46
import ThetaL3S49
import ThetaL3S51
import ThetaL3S58
import ThetaL3S59
import ThetaL3S64
import ThetaL3S73
import ThetaL3S74
import ThetaL3S79
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_792 : Blocked tgt 8 s2_792 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_792 8 _ le
  decide +kernel
theorem b2_793 : Blocked tgt 8 s2_793 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_793 8 _ le
  decide +kernel
theorem b2_794 : Blocked tgt 8 s2_794 := by
  apply node_sound (nxt := [s3_3,a1533,a1301,s3_1191,s3_1067,s3_1045,a1534,a1535,a1536,a1537,a1538,s3_212,a1539,s3_1192,s3_1113,s3_1096,s3_1093,a1540,s3_1544,a1541,s3_799,a1542,s3_1541,s3_1402,a1543,a1544,s3_1752,s3_1403,a1545,a1546,a1547,a1548,a1549,a1550,a1551,a1552,s3_232,a1553,a1554,a1555,s3_1405,a1556,a1557])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_746
    · exact via sym2 fix2 (by decide +kernel) b3_745
    · exact b3_1191
    · exact b3_1067
    · exact b3_1045
    · exact via sym2 fix2 (by decide +kernel) b3_1896
    · exact via sym2 fix2 (by decide +kernel) b3_1233
    · exact via sym2 fix2 (by decide +kernel) b3_804
    · exact via sym1 fix1 (by decide +kernel) b3_212
    · exact via sym2 fix2 (by decide +kernel) b3_1897
    · exact b3_212
    · exact via sym3 fix3 (by decide +kernel) b3_1897
    · exact b3_1192
    · exact b3_1113
    · exact b3_1096
    · exact b3_1093
    · exact via sym2 fix2 (by decide +kernel) b3_847
    · exact b3_1544
    · exact via sym2 fix2 (by decide +kernel) b3_1243
    · exact b3_799
    · exact via sym2 fix2 (by decide +kernel) b3_771
    · exact b3_1541
    · exact b3_1402
    · exact via sym1 fix1 (by decide +kernel) b3_232
    · exact via sym2 fix2 (by decide +kernel) b3_860
    · exact b3_1752
    · exact b3_1403
    · exact via sym3 fix3 (by decide +kernel) b3_387
    · exact via sym2 fix2 (by decide +kernel) b3_859
    · exact via sym2 fix2 (by decide +kernel) b3_1777
    · exact via sym1 fix1 (by decide +kernel) b3_1403
    · exact via sym2 fix2 (by decide +kernel) b3_387
    · exact via sym3 fix3 (by decide +kernel) b3_859
    · exact via sym3 fix3 (by decide +kernel) b3_1777
    · exact via sym1 fix1 (by decide +kernel) b3_1402
    · exact b3_232
    · exact via sym3 fix3 (by decide +kernel) b3_860
    · exact via sym1 fix1 (by decide +kernel) b3_1752
    · exact via sym3 fix3 (by decide +kernel) b3_281
    · exact b3_1405
    · exact via sym2 fix2 (by decide +kernel) b3_281
    · exact via sym1 fix1 (by decide +kernel) b3_1405
theorem b2_795 : Blocked tgt 8 s2_795 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s2_795 8 _ le
  decide +kernel
theorem b2_796 : Blocked tgt 8 s2_796 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_796 8 _ le
  decide +kernel
theorem b2_797 : Blocked tgt 8 s2_797 := by
  apply node_sound (nxt := [s3_1070,a1558,a1559,s3_1228,s3_798,a1560,s3_2,a1561,a1562,a1563,s3_213,a1564,a1565,s3_1427,s3_1113,s3_1100,s3_1094,s3_1190,a1566,a1567,a1568,a1569,a1570,a1571,s3_1418,s3_797,a1572,s3_1429,a1573,a1574,s3_1416,a1575,s3_763,s3_1423,a1576,a1577,a1578,a1579,a1580,a1581,a1582,a1583,a1584,s3_402,a1585,a1586])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1070
    · exact via sym2 fix2 (by decide +kernel) b3_1427
    · exact via sym2 fix2 (by decide +kernel) b3_1228
    · exact b3_1228
    · exact b3_798
    · exact via sym2 fix2 (by decide +kernel) b3_798
    · exact b3_2
    · exact via sym2 fix2 (by decide +kernel) b3_797
    · exact via sym1 fix1 (by decide +kernel) b3_213
    · exact via sym2 fix2 (by decide +kernel) b3_1429
    · exact b3_213
    · exact via sym3 fix3 (by decide +kernel) b3_1429
    · exact via sym2 fix2 (by decide +kernel) b3_1070
    · exact b3_1427
    · exact b3_1113
    · exact b3_1100
    · exact b3_1094
    · exact b3_1190
    · exact via sym1 fix1 (by decide +kernel) b3_1418
    · exact via sym2 fix2 (by decide +kernel) b3_1190
    · exact via sym3 fix3 (by decide +kernel) b3_1418
    · exact via sym3 fix3 (by decide +kernel) b3_1190
    · exact via sym2 fix2 (by decide +kernel) b3_1418
    · exact via sym1 fix1 (by decide +kernel) b3_1190
    · exact b3_1418
    · exact b3_797
    · exact via sym3 fix3 (by decide +kernel) b3_213
    · exact b3_1429
    · exact via sym2 fix2 (by decide +kernel) b3_213
    · exact via sym1 fix1 (by decide +kernel) b3_1429
    · exact b3_1416
    · exact via sym1 fix1 (by decide +kernel) b3_402
    · exact b3_763
    · exact b3_1423
    · exact via sym2 fix2 (by decide +kernel) b3_1416
    · exact via sym3 fix3 (by decide +kernel) b3_402
    · exact via sym2 fix2 (by decide +kernel) b3_763
    · exact via sym2 fix2 (by decide +kernel) b3_1423
    · exact via sym3 fix3 (by decide +kernel) b3_1416
    · exact via sym2 fix2 (by decide +kernel) b3_402
    · exact via sym3 fix3 (by decide +kernel) b3_763
    · exact via sym3 fix3 (by decide +kernel) b3_1423
    · exact via sym1 fix1 (by decide +kernel) b3_1416
    · exact b3_402
    · exact via sym1 fix1 (by decide +kernel) b3_763
    · exact via sym1 fix1 (by decide +kernel) b3_1423
theorem b2_798 : Blocked tgt 8 s2_798 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_798 8 _ le
  decide +kernel
theorem b2_799 : Blocked tgt 8 s2_799 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_799 8 _ le
  decide +kernel
theorem b2_800 : Blocked tgt 8 s2_800 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_800 8 _ le
  decide +kernel
theorem b2_801 : Blocked tgt 8 s2_801 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_801 8 _ le
  decide +kernel
theorem b2_802 : Blocked tgt 8 s2_802 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_802 8 _ le
  decide +kernel
theorem b2_803 : Blocked tgt 8 s2_803 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_803 8 _ le
  decide +kernel
theorem b2_804 : Blocked tgt 8 s2_804 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_804 8 _ le
  decide +kernel
theorem b2_805 : Blocked tgt 8 s2_805 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_805 8 _ le
  decide +kernel
theorem b2_806 : Blocked tgt 8 s2_806 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_806 8 _ le
  decide +kernel
theorem b2_807 : Blocked tgt 8 s2_807 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_807 8 _ le
  decide +kernel
theorem b2_808 : Blocked tgt 8 s2_808 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s2_808 8 _ le
  decide +kernel
theorem b2_809 : Blocked tgt 8 s2_809 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s2_809 8 _ le
  decide +kernel
theorem b2_810 : Blocked tgt 8 s2_810 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s2_810 8 _ le
  decide +kernel
theorem b2_811 : Blocked tgt 8 s2_811 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_811 8 _ le
  decide +kernel
theorem b2_812 : Blocked tgt 8 s2_812 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_812 8 _ le
  decide +kernel
theorem b2_813 : Blocked tgt 8 s2_813 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s2_813 8 _ le
  decide +kernel
theorem b2_814 : Blocked tgt 8 s2_814 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s2_814 8 _ le
  decide +kernel
theorem b2_815 : Blocked tgt 8 s2_815 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s2_815 8 _ le
  decide +kernel
end ThetaCert
