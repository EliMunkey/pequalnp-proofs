import ThetaAlias
import ThetaL3S0
import ThetaL3S2
import ThetaL3S5
import ThetaL3S8
import ThetaL3S9
import ThetaL3S15
import ThetaL3S16
import ThetaL3S32
import ThetaL3S33
import ThetaL3S34
import ThetaL3S36
import ThetaL3S37
import ThetaL3S38
import ThetaL3S39
import ThetaL3S44
import ThetaL3S45
import ThetaL3S50
import ThetaL3S51
import ThetaL3S52
import ThetaL3S53
import ThetaL3S54
import ThetaL3S55
import ThetaL3S56
import ThetaL3S63
import ThetaL3S64
import ThetaL3S72
import ThetaL3S73
import ThetaL3S74
import ThetaL3S78
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_768 : Blocked tgt 8 s2_768 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_768 8 _ le
  decide +kernel
theorem b2_769 : Blocked tgt 8 s2_769 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_769 8 _ le
  decide +kernel
theorem b2_770 : Blocked tgt 8 s2_770 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s2_770 8 _ le
  decide +kernel
theorem b2_771 : Blocked tgt 8 s2_771 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s2_771 8 _ le
  decide +kernel
theorem b2_772 : Blocked tgt 8 s2_772 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s2_772 8 _ le
  decide +kernel
theorem b2_773 : Blocked tgt 8 s2_773 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_773 8 _ le
  decide +kernel
theorem b2_774 : Blocked tgt 8 s2_774 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_774 8 _ le
  decide +kernel
theorem b2_775 : Blocked tgt 8 s2_775 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_775 8 _ le
  decide +kernel
theorem b2_776 : Blocked tgt 8 s2_776 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_776 8 _ le
  decide +kernel
theorem b2_777 : Blocked tgt 8 s2_777 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_777 8 _ le
  decide +kernel
theorem b2_778 : Blocked tgt 8 s2_778 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_778 8 _ le
  decide +kernel
theorem b2_779 : Blocked tgt 8 s2_779 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_779 8 _ le
  decide +kernel
theorem b2_780 : Blocked tgt 8 s2_780 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_780 8 _ le
  decide +kernel
theorem b2_781 : Blocked tgt 8 s2_781 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_781 8 _ le
  decide +kernel
theorem b2_782 : Blocked tgt 8 s2_782 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_782 8 _ le
  decide +kernel
theorem b2_783 : Blocked tgt 8 s2_783 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s2_783 8 _ le
  decide +kernel
theorem b2_784 : Blocked tgt 8 s2_784 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_784 8 _ le
  decide +kernel
theorem b2_785 : Blocked tgt 8 s2_785 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_785 8 _ le
  decide +kernel
theorem b2_786 : Blocked tgt 8 s2_786 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_786 8 _ le
  decide +kernel
theorem b2_787 : Blocked tgt 8 s2_787 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_787 8 _ le
  decide +kernel
theorem b2_788 : Blocked tgt 8 s2_788 := by
  intro m le c
  apply rejects_sound extra74 i5 4 tgt small74 hot74 [] s2_788 8 _ le
  decide +kernel
theorem b2_789 : Blocked tgt 8 s2_789 := by
  apply node_sound (nxt := [s3_3,s3_136,s3_133,s3_1065,a934,a1491,a1492,a1493,a1494,s3_208,a1495,s3_1216,s3_1215,s3_1214,s3_1080,s3_1079,s3_1078,a1496,s3_1528,s3_1242,s3_799,a1497,s3_1541,s3_1266,a1498,a1499,s3_1749,s3_1314,a1500,a1501,a938,s3_1343,a1502,a1503,a1504,a917,s3_404,a1505,a960,a1506,s3_1363])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact b3_136
    · exact b3_133
    · exact b3_1065
    · exact via sym2 fix2 (by decide +kernel) b3_1893
    · exact via sym2 fix2 (by decide +kernel) b3_1232
    · exact via sym2 fix2 (by decide +kernel) b3_803
    · exact via sym1 fix1 (by decide +kernel) b3_211
    · exact via sym2 fix2 (by decide +kernel) b3_1894
    · exact b3_208
    · exact via sym2 fix2 (by decide +kernel) b3_1895
    · exact b3_1216
    · exact b3_1215
    · exact b3_1214
    · exact b3_1080
    · exact b3_1079
    · exact b3_1078
    · exact via sym3 fix3 (by decide +kernel) b3_838
    · exact b3_1528
    · exact b3_1242
    · exact b3_799
    · exact via sym3 fix3 (by decide +kernel) b3_777
    · exact b3_1541
    · exact b3_1266
    · exact via sym1 fix1 (by decide +kernel) b3_228
    · exact via sym2 fix2 (by decide +kernel) b3_930
    · exact b3_1749
    · exact b3_1314
    · exact via sym3 fix3 (by decide +kernel) b3_385
    · exact via sym2 fix2 (by decide +kernel) b3_872
    · exact via sym2 fix2 (by decide +kernel) b3_1775
    · exact b3_1343
    · exact via sym2 fix2 (by decide +kernel) b3_384
    · exact via sym3 fix3 (by decide +kernel) b3_869
    · exact via sym3 fix3 (by decide +kernel) b3_1776
    · exact via sym1 fix1 (by decide +kernel) b3_1250
    · exact b3_404
    · exact via sym3 fix3 (by decide +kernel) b3_941
    · exact via sym1 fix1 (by decide +kernel) b3_1778
    · exact via sym2 fix2 (by decide +kernel) b3_214
    · exact b3_1363
theorem b2_790 : Blocked tgt 8 s2_790 := by
  apply node_sound (nxt := [s3_3,a1507,a1508,s3_1066,a1509,a1510,a1511,a1512,a1513,s3_1306,a1514,a1515,a1516,s3_209,a1517,s3_1223,s3_1082,a1518,s3_1529,a1519,s3_799,a1520,s3_1541,s3_1274,a1521,a1522,s3_1750,s3_1322,a1523,a1524,a1525,a1526,a1527,a1528,a1529,a1530,s3_226,a1531,a1532])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_70
    · exact via sym2 fix2 (by decide +kernel) b3_68
    · exact b3_1066
    · exact via sym2 fix2 (by decide +kernel) b3_1889
    · exact via sym2 fix2 (by decide +kernel) b3_1231
    · exact via sym2 fix2 (by decide +kernel) b3_802
    · exact via sym1 fix1 (by decide +kernel) b3_210
    · exact via sym2 fix2 (by decide +kernel) b3_1890
    · exact b3_1306
    · exact via sym2 fix2 (by decide +kernel) b3_896
    · exact via sym2 fix2 (by decide +kernel) b3_376
    · exact via sym2 fix2 (by decide +kernel) b3_1892
    · exact b3_209
    · exact via sym2 fix2 (by decide +kernel) b3_1891
    · exact b3_1223
    · exact b3_1082
    · exact via sym3 fix3 (by decide +kernel) b3_836
    · exact b3_1529
    · exact via sym2 fix2 (by decide +kernel) b3_1240
    · exact b3_799
    · exact via sym3 fix3 (by decide +kernel) b3_774
    · exact b3_1541
    · exact b3_1274
    · exact via sym1 fix1 (by decide +kernel) b3_227
    · exact via sym3 fix3 (by decide +kernel) b3_905
    · exact b3_1750
    · exact b3_1322
    · exact via sym3 fix3 (by decide +kernel) b3_386
    · exact via sym2 fix2 (by decide +kernel) b3_876
    · exact via sym2 fix2 (by decide +kernel) b3_1774
    · exact via sym1 fix1 (by decide +kernel) b3_1290
    · exact via sym2 fix2 (by decide +kernel) b3_404
    · exact via sym3 fix3 (by decide +kernel) b3_885
    · exact via sym3 fix3 (by decide +kernel) b3_1778
    · exact via sym1 fix1 (by decide +kernel) b3_1277
    · exact b3_226
    · exact via sym3 fix3 (by decide +kernel) b3_904
    · exact via sym1 fix1 (by decide +kernel) b3_1751
theorem b2_791 : Blocked tgt 8 s2_791 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_791 8 _ le
  decide +kernel
end ThetaCert
