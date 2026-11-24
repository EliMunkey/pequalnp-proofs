import ThetaAlias
import ThetaL3S0
import ThetaL3S3
import ThetaL3S5
import ThetaL3S6
import ThetaL3S7
import ThetaL3S8
import ThetaL3S10
import ThetaL3S14
import ThetaL3S18
import ThetaL3S22
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S34
import ThetaL3S35
import ThetaL3S36
import ThetaL3S38
import ThetaL3S39
import ThetaL3S40
import ThetaL3S41
import ThetaL3S42
import ThetaL3S49
import ThetaL3S50
import ThetaL3S51
import ThetaL3S52
import ThetaL3S53
import ThetaL3S54
import ThetaL3S55
import ThetaL3S58
import ThetaL3S62
import ThetaL3S70
import ThetaL3S71
import ThetaL3S72
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S80
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_576 : Blocked tgt 8 s2_576 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_576 8 _ le
  decide +kernel
theorem b2_577 : Blocked tgt 8 s2_577 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s2_577 8 _ le
  decide +kernel
theorem b2_578 : Blocked tgt 8 s2_578 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s2_578 8 _ le
  decide +kernel
theorem b2_579 : Blocked tgt 8 s2_579 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s2_579 8 _ le
  decide +kernel
theorem b2_580 : Blocked tgt 8 s2_580 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_580 8 _ le
  decide +kernel
theorem b2_581 : Blocked tgt 8 s2_581 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_581 8 _ le
  decide +kernel
theorem b2_582 : Blocked tgt 8 s2_582 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_582 8 _ le
  decide +kernel
theorem b2_583 : Blocked tgt 8 s2_583 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_583 8 _ le
  decide +kernel
theorem b2_584 : Blocked tgt 8 s2_584 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_584 8 _ le
  decide +kernel
theorem b2_585 : Blocked tgt 8 s2_585 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_585 8 _ le
  decide +kernel
theorem b2_586 : Blocked tgt 8 s2_586 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s2_586 8 _ le
  decide +kernel
theorem b2_587 : Blocked tgt 8 s2_587 := by
  apply node_sound (nxt := [s3_799,a1163,s3_1229,s3_1396,s3_839,s3_754,a1164,s3_1501,s3_3,a1165,s3_974,s3_870,a1166,a1167,s3_1699,s3_941,a1168,a1169,a1170,a1171,a1172,a1173,a1174,a1175,s3_79,a1176,a1177,a1178,s3_972,a1179,s3_975,s3_968,a1180,s3_967,s3_970,a1181,s3_973,a1182,s3_971])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_799
    · exact via sym2 fix2 (by decide +kernel) b3_764
    · exact b3_1229
    · exact b3_1396
    · exact b3_839
    · exact b3_754
    · exact via sym3 fix3 (by decide +kernel) b3_1211
    · exact b3_1501
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1778
    · exact b3_974
    · exact b3_870
    · exact via sym1 fix1 (by decide +kernel) b3_85
    · exact via sym3 fix3 (by decide +kernel) b3_1341
    · exact b3_1699
    · exact b3_941
    · exact via sym3 fix3 (by decide +kernel) b3_133
    · exact via sym2 fix2 (by decide +kernel) b3_1250
    · exact via sym2 fix2 (by decide +kernel) b3_1725
    · exact via sym1 fix1 (by decide +kernel) b3_931
    · exact via sym2 fix2 (by decide +kernel) b3_143
    · exact via sym3 fix3 (by decide +kernel) b3_1264
    · exact via sym3 fix3 (by decide +kernel) b3_1737
    · exact via sym1 fix1 (by decide +kernel) b3_873
    · exact b3_79
    · exact via sym3 fix3 (by decide +kernel) b3_1312
    · exact via sym1 fix1 (by decide +kernel) b3_1704
    · exact via sym2 fix2 (by decide +kernel) b3_792
    · exact b3_972
    · exact via sym1 fix1 (by decide +kernel) b3_190
    · exact b3_975
    · exact b3_968
    · exact via sym3 fix3 (by decide +kernel) b3_353
    · exact b3_967
    · exact b3_970
    · exact via sym3 fix3 (by decide +kernel) b3_196
    · exact b3_973
    · exact via sym2 fix2 (by decide +kernel) b3_443
    · exact b3_971
theorem b2_588 : Blocked tgt 8 s2_588 := by
  intro m le c
  apply rejects_sound extra44 i5 4 tgt small44 hot44 [] s2_588 8 _ le
  decide +kernel
theorem b2_589 : Blocked tgt 8 s2_589 := by
  apply node_sound (nxt := [s3_778,a1183,a1184,s3_1397,s3_847,s3_753,a1120,s3_979,s3_1936,s3_1500,s3_985,s3_3,a1185,s3_983,s3_871,a1186,a1187,s3_1700,s3_941,a1188,a1169,a1189,a1190,a1191,a1192,a1193,a1194,s3_80,a1195,a1196,s3_977,s3_976,s3_981,a1197,s3_986,s3_255,s3_987,a1198,s3_982])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_778
    · exact via sym2 fix2 (by decide +kernel) b3_768
    · exact via sym3 fix3 (by decide +kernel) b3_1241
    · exact b3_1397
    · exact b3_847
    · exact b3_753
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact b3_979
    · exact b3_1936
    · exact b3_1500
    · exact b3_985
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1767
    · exact b3_983
    · exact b3_871
    · exact via sym1 fix1 (by decide +kernel) b3_86
    · exact via sym3 fix3 (by decide +kernel) b3_1342
    · exact b3_1700
    · exact b3_941
    · exact via sym3 fix3 (by decide +kernel) b3_127
    · exact via sym2 fix2 (by decide +kernel) b3_1250
    · exact via sym2 fix2 (by decide +kernel) b3_1724
    · exact via sym1 fix1 (by decide +kernel) b3_932
    · exact via sym2 fix2 (by decide +kernel) b3_142
    · exact via sym3 fix3 (by decide +kernel) b3_1265
    · exact via sym3 fix3 (by decide +kernel) b3_1736
    · exact via sym1 fix1 (by decide +kernel) b3_874
    · exact b3_80
    · exact via sym3 fix3 (by decide +kernel) b3_1313
    · exact via sym1 fix1 (by decide +kernel) b3_1705
    · exact b3_977
    · exact b3_976
    · exact b3_981
    · exact via sym1 fix1 (by decide +kernel) b3_256
    · exact b3_986
    · exact b3_255
    · exact b3_987
    · exact via sym3 fix3 (by decide +kernel) b3_195
    · exact b3_982
theorem b2_590 : Blocked tgt 8 s2_590 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s2_590 8 _ le
  decide +kernel
theorem b2_591 : Blocked tgt 8 s2_591 := by
  apply node_sound (nxt := [s3_779,s3_769,a1199,s3_1398,s3_840,s3_755,a1200,s3_1502,s3_3,a1201,s3_994,s3_885,a1202,a1135,s3_1703,s3_933,a1203,a1204,a1205,a1206,a1207,a1208,a1209,a1210,s3_87,a1211,a1212,a1213,s3_992,a1214,s3_993,s3_441,s3_991,a1215,s3_990])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_779
    · exact b3_769
    · exact via sym1 fix1 (by decide +kernel) b3_1236
    · exact b3_1398
    · exact b3_840
    · exact b3_755
    · exact via sym2 fix2 (by decide +kernel) b3_1206
    · exact b3_1502
    · exact b3_3
    · exact via sym3 fix3 (by decide +kernel) b3_1795
    · exact b3_994
    · exact b3_885
    · exact via sym1 fix1 (by decide +kernel) b3_78
    · exact via sym2 fix2 (by decide +kernel) b3_1290
    · exact b3_1703
    · exact b3_933
    · exact via sym3 fix3 (by decide +kernel) b3_155
    · exact via sym2 fix2 (by decide +kernel) b3_1259
    · exact via sym2 fix2 (by decide +kernel) b3_1738
    · exact via sym1 fix1 (by decide +kernel) b3_941
    · exact via sym2 fix2 (by decide +kernel) b3_145
    · exact via sym3 fix3 (by decide +kernel) b3_1250
    · exact via sym3 fix3 (by decide +kernel) b3_1729
    · exact via sym1 fix1 (by decide +kernel) b3_879
    · exact b3_87
    · exact via sym3 fix3 (by decide +kernel) b3_1319
    · exact via sym1 fix1 (by decide +kernel) b3_1710
    · exact via sym1 fix1 (by decide +kernel) b3_349
    · exact b3_992
    · exact via sym2 fix2 (by decide +kernel) b3_198
    · exact b3_993
    · exact b3_441
    · exact b3_991
    · exact via sym3 fix3 (by decide +kernel) b3_444
    · exact b3_990
theorem b2_592 : Blocked tgt 8 s2_592 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s2_592 8 _ le
  decide +kernel
theorem b2_593 : Blocked tgt 8 s2_593 := by
  apply node_sound (nxt := [s3_780,s3_770,a1216,s3_1400,s3_841,s3_756,a1217,a1218,s3_998,s3_1937,s3_1504,s3_1004,s3_3,s3_1810,s3_1002,s3_875,a1219,a1220,s3_1706,s3_941,a1221,a1169,a1222,a1206,a1223,a1208,a1224,a1225,s3_88,a1226,a1227,a1228,s3_1001,a1229,a1230,a1231,s3_1000,s3_533,a1232])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_780
    · exact b3_770
    · exact via sym2 fix2 (by decide +kernel) b3_1238
    · exact b3_1400
    · exact b3_841
    · exact b3_756
    · exact via sym2 fix2 (by decide +kernel) b3_1209
    · exact via sym2 fix2 (by decide +kernel) b3_1208
    · exact b3_998
    · exact b3_1937
    · exact b3_1504
    · exact b3_1004
    · exact b3_3
    · exact b3_1810
    · exact b3_1002
    · exact b3_875
    · exact via sym1 fix1 (by decide +kernel) b3_88
    · exact via sym2 fix2 (by decide +kernel) b3_1311
    · exact b3_1706
    · exact b3_941
    · exact via sym3 fix3 (by decide +kernel) b3_140
    · exact via sym2 fix2 (by decide +kernel) b3_1250
    · exact via sym2 fix2 (by decide +kernel) b3_1735
    · exact via sym1 fix1 (by decide +kernel) b3_941
    · exact via sym2 fix2 (by decide +kernel) b3_140
    · exact via sym3 fix3 (by decide +kernel) b3_1250
    · exact via sym3 fix3 (by decide +kernel) b3_1735
    · exact via sym1 fix1 (by decide +kernel) b3_875
    · exact b3_88
    · exact via sym3 fix3 (by decide +kernel) b3_1311
    · exact via sym1 fix1 (by decide +kernel) b3_1706
    · exact via sym3 fix3 (by decide +kernel) b3_197
    · exact b3_1001
    · exact via sym2 fix2 (by decide +kernel) b3_197
    · exact via sym1 fix1 (by decide +kernel) b3_1001
    · exact via sym1 fix1 (by decide +kernel) b3_533
    · exact b3_1000
    · exact b3_533
    · exact via sym1 fix1 (by decide +kernel) b3_1000
theorem b2_594 : Blocked tgt 8 s2_594 := by
  apply node_sound (nxt := [s3_781,a1233,s3_1237,s3_1401,s3_842,s3_757,a1234,s3_1505,s3_3,a998,s3_1011,s3_885,a1235,a1135,s3_1707,s3_934,a1236,a1237,a1238,a1239,a1240,a1241,a1242,a1243,s3_74,a954,a1244,a1245,s3_1009,s3_1007,s3_843,a1246,s3_1010,s3_348,a1247])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_781
    · exact via sym2 fix2 (by decide +kernel) b3_770
    · exact b3_1237
    · exact b3_1401
    · exact b3_842
    · exact b3_757
    · exact via sym2 fix2 (by decide +kernel) b3_1218
    · exact b3_1505
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1807
    · exact b3_1011
    · exact b3_885
    · exact via sym1 fix1 (by decide +kernel) b3_74
    · exact via sym2 fix2 (by decide +kernel) b3_1290
    · exact b3_1707
    · exact b3_934
    · exact via sym3 fix3 (by decide +kernel) b3_156
    · exact via sym2 fix2 (by decide +kernel) b3_1267
    · exact via sym2 fix2 (by decide +kernel) b3_1732
    · exact via sym1 fix1 (by decide +kernel) b3_934
    · exact via sym2 fix2 (by decide +kernel) b3_156
    · exact via sym3 fix3 (by decide +kernel) b3_1267
    · exact via sym3 fix3 (by decide +kernel) b3_1732
    · exact via sym1 fix1 (by decide +kernel) b3_885
    · exact b3_74
    · exact via sym3 fix3 (by decide +kernel) b3_1290
    · exact via sym1 fix1 (by decide +kernel) b3_1707
    · exact via sym2 fix2 (by decide +kernel) b3_794
    · exact b3_1009
    · exact b3_1007
    · exact b3_843
    · exact via sym1 fix1 (by decide +kernel) b3_348
    · exact b3_1010
    · exact b3_348
    · exact via sym1 fix1 (by decide +kernel) b3_1010
theorem b2_595 : Blocked tgt 8 s2_595 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s2_595 8 _ le
  decide +kernel
theorem b2_596 : Blocked tgt 8 s2_596 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_596 8 _ le
  decide +kernel
theorem b2_597 : Blocked tgt 8 s2_597 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_597 8 _ le
  decide +kernel
theorem b2_598 : Blocked tgt 8 s2_598 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_598 8 _ le
  decide +kernel
theorem b2_599 : Blocked tgt 8 s2_599 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_599 8 _ le
  decide +kernel
end ThetaCert
