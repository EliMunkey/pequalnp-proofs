import ThetaAlias
import ThetaL3S0
import ThetaL3S3
import ThetaL3S4
import ThetaL3S11
import ThetaL3S12
import ThetaL3S13
import ThetaL3S17
import ThetaL3S25
import ThetaL3S31
import ThetaL3S33
import ThetaL3S35
import ThetaL3S36
import ThetaL3S39
import ThetaL3S42
import ThetaL3S43
import ThetaL3S44
import ThetaL3S45
import ThetaL3S46
import ThetaL3S47
import ThetaL3S49
import ThetaL3S50
import ThetaL3S51
import ThetaL3S59
import ThetaL3S60
import ThetaL3S61
import ThetaL3S62
import ThetaL3S63
import ThetaL3S64
import ThetaL3S73
import ThetaL3S74
import ThetaL3S80
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_816 : Blocked tgt 8 s2_816 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_816 8 _ le
  decide +kernel
theorem b2_817 : Blocked tgt 8 s2_817 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_817 8 _ le
  decide +kernel
theorem b2_818 : Blocked tgt 8 s2_818 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_818 8 _ le
  decide +kernel
theorem b2_819 : Blocked tgt 8 s2_819 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_819 8 _ le
  decide +kernel
theorem b2_820 : Blocked tgt 8 s2_820 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_820 8 _ le
  decide +kernel
theorem b2_821 : Blocked tgt 8 s2_821 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_821 8 _ le
  decide +kernel
theorem b2_822 : Blocked tgt 8 s2_822 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(2,true))] s2_822 8 _ le
  decide +kernel
theorem b2_823 : Blocked tgt 8 s2_823 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_823 8 _ le
  decide +kernel
theorem b2_824 : Blocked tgt 8 s2_824 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s2_824 8 _ le
  decide +kernel
theorem b2_825 : Blocked tgt 8 s2_825 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_825 8 _ le
  decide +kernel
theorem b2_826 : Blocked tgt 8 s2_826 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(4,true))] s2_826 8 _ le
  decide +kernel
theorem b2_827 : Blocked tgt 8 s2_827 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_827 8 _ le
  decide +kernel
theorem b2_828 : Blocked tgt 8 s2_828 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(3,true),(4,true))] s2_828 8 _ le
  decide +kernel
theorem b2_829 : Blocked tgt 8 s2_829 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_829 8 _ le
  decide +kernel
theorem b2_830 : Blocked tgt 8 s2_830 := by
  apply node_sound (nxt := [s3_1195,s3_1051,s3_1213,a1587,a1540,s3_1524,s3_806,a912,a1588,s3_1478,s3_3,s3_98,s3_95,a1589,s3_1927,a1590,s3_1928,s3_274,s3_1929,a1591,s3_857,a1592,a908,s3_1443,a1593,s3_1126,s3_1758,a1594,a1595,a1596,a1597,a1598,a1599,a1600,a1601,a918,s3_321,a1602,a925])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1195
    · exact b3_1051
    · exact b3_1213
    · exact via sym1 fix1 (by decide +kernel) b3_1022
    · exact via sym2 fix2 (by decide +kernel) b3_847
    · exact b3_1524
    · exact b3_806
    · exact via sym2 fix2 (by decide +kernel) b3_1490
    · exact via sym3 fix3 (by decide +kernel) b3_940
    · exact b3_1478
    · exact b3_3
    · exact b3_98
    · exact b3_95
    · exact via sym3 fix3 (by decide +kernel) b3_277
    · exact b3_1927
    · exact via sym2 fix2 (by decide +kernel) b3_276
    · exact b3_1928
    · exact b3_274
    · exact b3_1929
    · exact via sym2 fix2 (by decide +kernel) b3_1221
    · exact b3_857
    · exact via sym3 fix3 (by decide +kernel) b3_1027
    · exact via sym2 fix2 (by decide +kernel) b3_1529
    · exact b3_1443
    · exact via sym1 fix1 (by decide +kernel) b3_300
    · exact b3_1126
    · exact b3_1758
    · exact via sym2 fix2 (by decide +kernel) b3_1453
    · exact via sym3 fix3 (by decide +kernel) b3_299
    · exact via sym2 fix2 (by decide +kernel) b3_1120
    · exact via sym2 fix2 (by decide +kernel) b3_1761
    · exact via sym3 fix3 (by decide +kernel) b3_1457
    · exact via sym2 fix2 (by decide +kernel) b3_297
    · exact via sym3 fix3 (by decide +kernel) b3_1116
    · exact via sym3 fix3 (by decide +kernel) b3_1763
    · exact via sym1 fix1 (by decide +kernel) b3_1431
    · exact b3_321
    · exact via sym1 fix1 (by decide +kernel) b3_1130
    · exact via sym1 fix1 (by decide +kernel) b3_1767
theorem b2_831 : Blocked tgt 8 s2_831 := by
  apply node_sound (nxt := [s3_1212,a931,a1603,s3_1528,a1604,s3_1481,s3_3,s3_105,s3_101,a1605,a1606,a1607,s3_1930,s3_275,s3_1931,a1608,s3_847,a1609,a1610,s3_1444,a1611,s3_1125,s3_1759,a1612,a1613,a1614,a943,a1615,a1616,a1617,a1618,a918,s3_418,a1602,a970,a1619,s3_1482,s3_1479,s3_604])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1212
    · exact via sym1 fix1 (by decide +kernel) b3_1024
    · exact via sym2 fix2 (by decide +kernel) b3_858
    · exact b3_1528
    · exact via sym3 fix3 (by decide +kernel) b3_939
    · exact b3_1481
    · exact b3_3
    · exact b3_105
    · exact b3_101
    · exact via sym2 fix2 (by decide +kernel) b3_1196
    · exact via sym2 fix2 (by decide +kernel) b3_1052
    · exact via sym1 fix1 (by decide +kernel) b3_278
    · exact b3_1930
    · exact b3_275
    · exact b3_1931
    · exact via sym2 fix2 (by decide +kernel) b3_1222
    · exact b3_847
    · exact via sym3 fix3 (by decide +kernel) b3_1026
    · exact via sym2 fix2 (by decide +kernel) b3_1524
    · exact b3_1444
    · exact via sym1 fix1 (by decide +kernel) b3_301
    · exact b3_1125
    · exact b3_1759
    · exact via sym2 fix2 (by decide +kernel) b3_1452
    · exact via sym3 fix3 (by decide +kernel) b3_298
    · exact via sym2 fix2 (by decide +kernel) b3_1121
    · exact via sym2 fix2 (by decide +kernel) b3_1760
    · exact via sym3 fix3 (by decide +kernel) b3_1456
    · exact via sym2 fix2 (by decide +kernel) b3_296
    · exact via sym3 fix3 (by decide +kernel) b3_1117
    · exact via sym3 fix3 (by decide +kernel) b3_1762
    · exact via sym1 fix1 (by decide +kernel) b3_1431
    · exact b3_418
    · exact via sym1 fix1 (by decide +kernel) b3_1130
    · exact via sym1 fix1 (by decide +kernel) b3_1779
    · exact via sym1 fix1 (by decide +kernel) b3_884
    · exact b3_1482
    · exact b3_1479
    · exact b3_604
theorem b2_832 : Blocked tgt 8 s2_832 := by
  apply node_sound (nxt := [s3_1197,s3_1053,s3_1224,s3_1019,a1540,s3_1524,a1620,s3_1495,s3_3,s3_748,s3_745,s3_850,s3_1932,a1621,s3_1933,a1622,a1623,a1120,s3_864,a1302,s3_1544,s3_1492,a1624,a1625,s3_1764,s3_1493,a1626,a1627,a1628,a1629,a1630,a1631,a1632,a1633,s3_302,a1634,a1635])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1197
    · exact b3_1053
    · exact b3_1224
    · exact b3_1019
    · exact via sym2 fix2 (by decide +kernel) b3_847
    · exact b3_1524
    · exact via sym2 fix2 (by decide +kernel) b3_807
    · exact b3_1495
    · exact b3_3
    · exact b3_748
    · exact b3_745
    · exact b3_850
    · exact b3_1932
    · exact via sym3 fix3 (by decide +kernel) b3_279
    · exact b3_1933
    · exact via sym2 fix2 (by decide +kernel) b3_279
    · exact via sym1 fix1 (by decide +kernel) b3_1933
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact b3_864
    · exact via sym2 fix2 (by decide +kernel) b3_1048
    · exact b3_1544
    · exact b3_1492
    · exact via sym1 fix1 (by decide +kernel) b3_302
    · exact via sym2 fix2 (by decide +kernel) b3_1084
    · exact b3_1764
    · exact b3_1493
    · exact via sym3 fix3 (by decide +kernel) b3_307
    · exact via sym2 fix2 (by decide +kernel) b3_1083
    · exact via sym2 fix2 (by decide +kernel) b3_1765
    · exact via sym1 fix1 (by decide +kernel) b3_1493
    · exact via sym2 fix2 (by decide +kernel) b3_307
    · exact via sym3 fix3 (by decide +kernel) b3_1083
    · exact via sym3 fix3 (by decide +kernel) b3_1765
    · exact via sym1 fix1 (by decide +kernel) b3_1492
    · exact b3_302
    · exact via sym3 fix3 (by decide +kernel) b3_1084
    · exact via sym1 fix1 (by decide +kernel) b3_1764
theorem b2_833 : Blocked tgt 8 s2_833 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_833 8 _ le
  decide +kernel
theorem b2_834 : Blocked tgt 8 s2_834 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_834 8 _ le
  decide +kernel
theorem b2_835 : Blocked tgt 8 s2_835 := by
  apply node_sound (nxt := [s3_1198,s3_1056,s3_1244,s3_745,a1540,s3_1524,s3_810,a1636,a1637,s3_1508,s3_3,s3_1021,s3_1019,a1638,a1639,a1640,s3_1938,a1641,a1642,a1643,a1644,s3_280,a1645,a1646,s3_847,a1301,a1610,s3_1507,a1647,s3_1017,s3_1766,a1648,a1649,a1650,a1651,a1652,a1653,a1654,a1655,a1656,s3_312,a1657,a1658])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1198
    · exact b3_1056
    · exact b3_1244
    · exact b3_745
    · exact via sym2 fix2 (by decide +kernel) b3_847
    · exact b3_1524
    · exact b3_810
    · exact via sym2 fix2 (by decide +kernel) b3_810
    · exact via sym2 fix2 (by decide +kernel) b3_1508
    · exact b3_1508
    · exact b3_3
    · exact b3_1021
    · exact b3_1019
    · exact via sym2 fix2 (by decide +kernel) b3_1198
    · exact via sym2 fix2 (by decide +kernel) b3_1056
    · exact via sym1 fix1 (by decide +kernel) b3_280
    · exact b3_1938
    · exact via sym3 fix3 (by decide +kernel) b3_280
    · exact via sym2 fix2 (by decide +kernel) b3_1938
    · exact via sym2 fix2 (by decide +kernel) b3_280
    · exact via sym3 fix3 (by decide +kernel) b3_1938
    · exact b3_280
    · exact via sym1 fix1 (by decide +kernel) b3_1938
    · exact via sym2 fix2 (by decide +kernel) b3_1244
    · exact b3_847
    · exact via sym2 fix2 (by decide +kernel) b3_745
    · exact via sym2 fix2 (by decide +kernel) b3_1524
    · exact b3_1507
    · exact via sym1 fix1 (by decide +kernel) b3_312
    · exact b3_1017
    · exact b3_1766
    · exact via sym2 fix2 (by decide +kernel) b3_1507
    · exact via sym3 fix3 (by decide +kernel) b3_312
    · exact via sym2 fix2 (by decide +kernel) b3_1017
    · exact via sym2 fix2 (by decide +kernel) b3_1766
    · exact via sym3 fix3 (by decide +kernel) b3_1507
    · exact via sym2 fix2 (by decide +kernel) b3_312
    · exact via sym3 fix3 (by decide +kernel) b3_1017
    · exact via sym3 fix3 (by decide +kernel) b3_1766
    · exact via sym1 fix1 (by decide +kernel) b3_1507
    · exact b3_312
    · exact via sym1 fix1 (by decide +kernel) b3_1017
    · exact via sym1 fix1 (by decide +kernel) b3_1766
theorem b2_836 : Blocked tgt 8 s2_836 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_836 8 _ le
  decide +kernel
theorem b2_837 : Blocked tgt 8 s2_837 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_837 8 _ le
  decide +kernel
theorem b2_838 : Blocked tgt 8 s2_838 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_838 8 _ le
  decide +kernel
theorem b2_839 : Blocked tgt 8 s2_839 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_839 8 _ le
  decide +kernel
end ThetaCert
