import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S4
import ThetaL3S5
import ThetaL3S9
import ThetaL3S16
import ThetaL3S17
import ThetaL3S28
import ThetaL3S29
import ThetaL3S30
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S34
import ThetaL3S36
import ThetaL3S38
import ThetaL3S40
import ThetaL3S42
import ThetaL3S44
import ThetaL3S45
import ThetaL3S46
import ThetaL3S48
import ThetaL3S51
import ThetaL3S53
import ThetaL3S55
import ThetaL3S56
import ThetaL3S58
import ThetaL3S59
import ThetaL3S61
import ThetaL3S63
import ThetaL3S64
import ThetaL3S74
import ThetaL3S75
import ThetaL3S78
import ThetaL3S79
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_864 : Blocked tgt 8 s2_864 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s2_864 8 _ le
  decide +kernel
theorem b2_865 : Blocked tgt 8 s2_865 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s2_865 8 _ le
  decide +kernel
theorem b2_866 : Blocked tgt 8 s2_866 := by
  apply node_sound (nxt := [s3_834,a1679,s3_1420,s3_1106,a1680,s3_914,s3_1531,a1681,s3_1534,a1682,s3_764,s3_1778,a1683,a1684])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_834
    · exact via sym1 fix1 (by decide +kernel) b3_218
    · exact b3_1420
    · exact b3_1106
    · exact via sym2 fix2 (by decide +kernel) b3_1338
    · exact b3_914
    · exact b3_1531
    · exact via sym1 fix1 (by decide +kernel) b3_405
    · exact b3_1534
    · exact via sym1 fix1 (by decide +kernel) b3_133
    · exact b3_764
    · exact b3_1778
    · exact via sym2 fix2 (by decide +kernel) b3_1539
    · exact via sym3 fix3 (by decide +kernel) b3_680
theorem b2_867 : Blocked tgt 8 s2_867 := by
  apply node_sound (nxt := [s3_1077,a1685,a1289,a1686,s3_1963,s3_1421,s3_1107,s3_765,a1687,s3_1535,a1304,s3_768,s3_1780])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1077
    · exact via sym3 fix3 (by decide +kernel) b3_1916
    · exact via sym1 fix1 (by decide +kernel) b3_99
    · exact via sym2 fix2 (by decide +kernel) b3_1914
    · exact b3_1963
    · exact b3_1421
    · exact b3_1107
    · exact b3_765
    · exact via sym1 fix1 (by decide +kernel) b3_1873
    · exact b3_1535
    · exact via sym1 fix1 (by decide +kernel) b3_110
    · exact b3_768
    · exact b3_1780
theorem b2_868 : Blocked tgt 8 s2_868 := by
  apply node_sound (nxt := [s3_1288,a1688,s3_1422,s3_1108,s3_1532,a1689,s3_1536,a1083,s3_764,s3_1778])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1288
    · exact via sym2 fix2 (by decide +kernel) b3_972
    · exact b3_1422
    · exact b3_1108
    · exact b3_1532
    · exact via sym1 fix1 (by decide +kernel) b3_406
    · exact b3_1536
    · exact via sym1 fix1 (by decide +kernel) b3_68
    · exact b3_764
    · exact b3_1778
theorem b2_869 : Blocked tgt 8 s2_869 := by
  apply node_sound (nxt := [a1688,s3_1423,s3_1109,s3_1471,s3_1174,s3_914,s3_1533,a1690,s3_3,s3_764,a1691,a1692])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_972
    · exact b3_1423
    · exact b3_1109
    · exact b3_1471
    · exact b3_1174
    · exact b3_914
    · exact b3_1533
    · exact via sym1 fix1 (by decide +kernel) b3_407
    · exact b3_3
    · exact b3_764
    · exact via sym2 fix2 (by decide +kernel) b3_1540
    · exact via sym3 fix3 (by decide +kernel) b3_714
theorem b2_870 : Blocked tgt 8 s2_870 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_870 8 _ le
  decide +kernel
theorem b2_871 : Blocked tgt 8 s2_871 := by
  apply node_sound (nxt := [a1693,s3_1424,s3_1111,s3_1917,s3_1537,a1694,s3_769,s3_1798])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) b3_1917
    · exact b3_1424
    · exact b3_1111
    · exact b3_1917
    · exact b3_1537
    · exact via sym1 fix1 (by decide +kernel) b3_27
    · exact b3_769
    · exact b3_1798
theorem b2_872 : Blocked tgt 8 s2_872 := by
  apply node_sound (nxt := [s3_1351,a1695,s3_1425,s3_1112,a1696,s3_1918,a1697,s3_1915,a1698,a1699,a1700,a1701,s3_1538,a1702,s3_770,s3_1811])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1351
    · exact via sym2 fix2 (by decide +kernel) b3_1009
    · exact b3_1425
    · exact b3_1112
    · exact via sym1 fix1 (by decide +kernel) b3_1918
    · exact b3_1918
    · exact via sym2 fix2 (by decide +kernel) b3_45
    · exact b3_1915
    · exact via sym2 fix2 (by decide +kernel) b3_766
    · exact via sym3 fix3 (by decide +kernel) b3_1878
    · exact via sym3 fix3 (by decide +kernel) b3_766
    · exact via sym2 fix2 (by decide +kernel) b3_1878
    · exact b3_1538
    · exact via sym2 fix2 (by decide +kernel) b3_54
    · exact b3_770
    · exact b3_1811
theorem b2_873 : Blocked tgt 8 s2_873 := by
  apply node_sound (nxt := [s3_1073,a1094,a1703,s3_1234,s3_805,a1704,s3_3,a1705,a1706,a1103,s3_217,a916,a1298,s3_1907,s3_1426,s3_1417,s3_1413,s3_760,s3_1113,s3_1100,s3_1096,s3_1544,s3_799,a1707,s3_1913,a1708,a1709,s3_1530,a1710,s3_764,s3_1778,a1711,a1712,a1163,a1165,a1713,a1527,a1714,a1529,a952,s3_404,a1715,a960])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1073
    · exact via sym2 fix2 (by decide +kernel) b3_1907
    · exact via sym2 fix2 (by decide +kernel) b3_1234
    · exact b3_1234
    · exact b3_805
    · exact via sym2 fix2 (by decide +kernel) b3_805
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_799
    · exact via sym1 fix1 (by decide +kernel) b3_217
    · exact via sym2 fix2 (by decide +kernel) b3_1913
    · exact b3_217
    · exact via sym3 fix3 (by decide +kernel) b3_1913
    · exact via sym2 fix2 (by decide +kernel) b3_1073
    · exact b3_1907
    · exact b3_1426
    · exact b3_1417
    · exact b3_1413
    · exact b3_760
    · exact b3_1113
    · exact b3_1100
    · exact b3_1096
    · exact b3_1544
    · exact b3_799
    · exact via sym3 fix3 (by decide +kernel) b3_217
    · exact b3_1913
    · exact via sym2 fix2 (by decide +kernel) b3_217
    · exact via sym1 fix1 (by decide +kernel) b3_1913
    · exact b3_1530
    · exact via sym1 fix1 (by decide +kernel) b3_404
    · exact b3_764
    · exact b3_1778
    · exact via sym2 fix2 (by decide +kernel) b3_1530
    · exact via sym3 fix3 (by decide +kernel) b3_404
    · exact via sym2 fix2 (by decide +kernel) b3_764
    · exact via sym2 fix2 (by decide +kernel) b3_1778
    · exact via sym3 fix3 (by decide +kernel) b3_1530
    · exact via sym2 fix2 (by decide +kernel) b3_404
    · exact via sym3 fix3 (by decide +kernel) b3_764
    · exact via sym3 fix3 (by decide +kernel) b3_1778
    · exact via sym1 fix1 (by decide +kernel) b3_1530
    · exact b3_404
    · exact via sym1 fix1 (by decide +kernel) b3_764
    · exact via sym1 fix1 (by decide +kernel) b3_1778
theorem b2_874 : Blocked tgt 8 s2_874 := by
  apply node_sound (nxt := [s3_3,a1716,a1717,s3_1113,s3_1101,s3_1096,s3_867,s3_864,s3_1543,a1718,s3_737,s3_1780,a1719,a1720,a1721,a1671,a1722,a1723,a1724,a1725,a1726,s3_424,a1727,a1728])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_867
    · exact via sym2 fix2 (by decide +kernel) b3_864
    · exact b3_1113
    · exact b3_1101
    · exact b3_1096
    · exact b3_867
    · exact b3_864
    · exact b3_1543
    · exact via sym1 fix1 (by decide +kernel) b3_424
    · exact b3_737
    · exact b3_1780
    · exact via sym2 fix2 (by decide +kernel) b3_1543
    · exact via sym3 fix3 (by decide +kernel) b3_424
    · exact via sym2 fix2 (by decide +kernel) b3_737
    · exact via sym2 fix2 (by decide +kernel) b3_1780
    · exact via sym3 fix3 (by decide +kernel) b3_1543
    · exact via sym2 fix2 (by decide +kernel) b3_424
    · exact via sym3 fix3 (by decide +kernel) b3_737
    · exact via sym3 fix3 (by decide +kernel) b3_1780
    · exact via sym1 fix1 (by decide +kernel) b3_1543
    · exact b3_424
    · exact via sym1 fix1 (by decide +kernel) b3_737
    · exact via sym1 fix1 (by decide +kernel) b3_1780
theorem b2_875 : Blocked tgt 8 s2_875 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_875 8 _ le
  decide +kernel
theorem b2_876 : Blocked tgt 8 s2_876 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_876 8 _ le
  decide +kernel
theorem b2_877 : Blocked tgt 8 s2_877 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_877 8 _ le
  decide +kernel
theorem b2_878 : Blocked tgt 8 s2_878 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s2_878 8 _ le
  decide +kernel
theorem b2_879 : Blocked tgt 8 s2_879 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s2_879 8 _ le
  decide +kernel
theorem b2_880 : Blocked tgt 8 s2_880 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s2_880 8 _ le
  decide +kernel
theorem b2_881 : Blocked tgt 8 s2_881 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_881 8 _ le
  decide +kernel
theorem b2_882 : Blocked tgt 8 s2_882 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_882 8 _ le
  decide +kernel
theorem b2_883 : Blocked tgt 8 s2_883 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_883 8 _ le
  decide +kernel
theorem b2_884 : Blocked tgt 8 s2_884 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_884 8 _ le
  decide +kernel
theorem b2_885 : Blocked tgt 8 s2_885 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_885 8 _ le
  decide +kernel
theorem b2_886 : Blocked tgt 8 s2_886 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_886 8 _ le
  decide +kernel
theorem b2_887 : Blocked tgt 8 s2_887 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_887 8 _ le
  decide +kernel
end ThetaCert
