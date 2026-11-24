import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S4
import ThetaL3S7
import ThetaL3S8
import ThetaL3S10
import ThetaL3S16
import ThetaL3S20
import ThetaL3S25
import ThetaL3S30
import ThetaL3S31
import ThetaL3S32
import ThetaL3S35
import ThetaL3S36
import ThetaL3S38
import ThetaL3S40
import ThetaL3S42
import ThetaL3S43
import ThetaL3S44
import ThetaL3S45
import ThetaL3S46
import ThetaL3S49
import ThetaL3S50
import ThetaL3S51
import ThetaL3S58
import ThetaL3S59
import ThetaL3S62
import ThetaL3S64
import ThetaL3S71
import ThetaL3S74
import ThetaL3S75
import ThetaL3S76
import ThetaL3S79
import ThetaL3S80
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_624 : Blocked tgt 8 s2_624 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_624 8 _ le
  decide +kernel
theorem b2_625 : Blocked tgt 8 s2_625 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_625 8 _ le
  decide +kernel
theorem b2_626 : Blocked tgt 8 s2_626 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s2_626 8 _ le
  decide +kernel
theorem b2_627 : Blocked tgt 8 s2_627 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s2_627 8 _ le
  decide +kernel
theorem b2_628 : Blocked tgt 8 s2_628 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_628 8 _ le
  decide +kernel
theorem b2_629 : Blocked tgt 8 s2_629 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_629 8 _ le
  decide +kernel
theorem b2_630 : Blocked tgt 8 s2_630 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_630 8 _ le
  decide +kernel
theorem b2_631 : Blocked tgt 8 s2_631 := by
  apply node_sound (nxt := [s3_1025,a1076,a1263,s3_1777,a1264,s3_1047,s3_1040])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1025
    · exact via sym1 fix1 (by decide +kernel) b3_60
    · exact via sym2 fix2 (by decide +kernel) b3_1499
    · exact b3_1777
    · exact via sym1 fix1 (by decide +kernel) b3_1064
    · exact b3_1047
    · exact b3_1040
theorem b2_632 : Blocked tgt 8 s2_632 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s2_632 8 _ le
  decide +kernel
theorem b2_633 : Blocked tgt 8 s2_633 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_633 8 _ le
  decide +kernel
theorem b2_634 : Blocked tgt 8 s2_634 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_634 8 _ le
  decide +kernel
theorem b2_635 : Blocked tgt 8 s2_635 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_635 8 _ le
  decide +kernel
theorem b2_636 : Blocked tgt 8 s2_636 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_636 8 _ le
  decide +kernel
theorem b2_637 : Blocked tgt 8 s2_637 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_637 8 _ le
  decide +kernel
theorem b2_638 : Blocked tgt 8 s2_638 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s2_638 8 _ le
  decide +kernel
theorem b2_639 : Blocked tgt 8 s2_639 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_639 8 _ le
  decide +kernel
theorem b2_640 : Blocked tgt 8 s2_640 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_640 8 _ le
  decide +kernel
theorem b2_641 : Blocked tgt 8 s2_641 := by
  apply node_sound (nxt := [a1265,a1266,a1267,s3_1843,s3_1031,s3_35,a1268,a1269,s3_46,s3_1061])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1498
    · exact via sym1 fix1 (by decide +kernel) b3_1843
    · exact via sym3 fix3 (by decide +kernel) b3_1498
    · exact b3_1843
    · exact b3_1031
    · exact b3_35
    · exact via sym2 fix2 (by decide +kernel) b3_1503
    · exact via sym2 fix2 (by decide +kernel) b3_1804
    · exact b3_46
    · exact b3_1061
theorem b2_642 : Blocked tgt 8 s2_642 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_642 8 _ le
  decide +kernel
theorem b2_643 : Blocked tgt 8 s2_643 := by
  apply node_sound (nxt := [s3_1200,s3_1042,s3_749,a1270,s3_1023,a1271,s3_1054,a1272,a1273,a1274,s3_1055,s3_1060,a1275,a1276,a1277,a1278,s3_786,s3_1077,a1279,a1280,s3_1044,a1281,a1282,s3_881,a1264,s3_1057,a1259,a1283,a1284,s3_1058,a1285,s3_497,s3_1061])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1200
    · exact b3_1042
    · exact b3_749
    · exact via sym2 fix2 (by decide +kernel) b3_1405
    · exact b3_1023
    · exact via sym2 fix2 (by decide +kernel) b3_1934
    · exact b3_1054
    · exact via sym1 fix1 (by decide +kernel) b3_1062
    · exact via sym2 fix2 (by decide +kernel) b3_1936
    · exact via sym2 fix2 (by decide +kernel) b3_1935
    · exact b3_1055
    · exact b3_1060
    · exact via sym3 fix3 (by decide +kernel) b3_108
    · exact via sym2 fix2 (by decide +kernel) b3_1952
    · exact via sym2 fix2 (by decide +kernel) b3_107
    · exact via sym3 fix3 (by decide +kernel) b3_1953
    · exact b3_786
    · exact b3_1077
    · exact via sym2 fix2 (by decide +kernel) b3_935
    · exact via sym1 fix1 (by decide +kernel) b3_1063
    · exact b3_1044
    · exact via sym2 fix2 (by decide +kernel) b3_978
    · exact via sym2 fix2 (by decide +kernel) b3_977
    · exact b3_881
    · exact via sym1 fix1 (by decide +kernel) b3_1064
    · exact b3_1057
    · exact via sym1 fix1 (by decide +kernel) b3_100
    · exact via sym1 fix1 (by decide +kernel) b3_258
    · exact via sym1 fix1 (by decide +kernel) b3_257
    · exact b3_1058
    · exact via sym1 fix1 (by decide +kernel) b3_600
    · exact b3_497
    · exact b3_1061
theorem b2_644 : Blocked tgt 8 s2_644 := by
  apply node_sound (nxt := [a1094,s3_1076,a1286,s3_1018,s3_738,a1287,a1288,s3_1072,a1289,a1290,s3_99,a1291,s3_1068,s3_1037,a1262,s3_1036,s3_1074,s3_1071,s3_1070,s3_1069,s3_758,s3_1039,a1292,s3_1077,s3_259,a1293,s3_784,s3_783,a1294,s3_1075,a1295,a1296])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1907
    · exact b3_1076
    · exact via sym2 fix2 (by decide +kernel) b3_1020
    · exact b3_1018
    · exact b3_738
    · exact via sym2 fix2 (by decide +kernel) b3_1225
    · exact via sym2 fix2 (by decide +kernel) b3_1430
    · exact b3_1072
    · exact via sym1 fix1 (by decide +kernel) b3_99
    · exact via sym2 fix2 (by decide +kernel) b3_1911
    · exact b3_99
    · exact via sym3 fix3 (by decide +kernel) b3_1911
    · exact b3_1068
    · exact b3_1037
    · exact via sym2 fix2 (by decide +kernel) b3_1035
    · exact b3_1036
    · exact b3_1074
    · exact b3_1071
    · exact b3_1070
    · exact b3_1069
    · exact b3_758
    · exact b3_1039
    · exact via sym1 fix1 (by decide +kernel) b3_259
    · exact b3_1077
    · exact b3_259
    · exact via sym1 fix1 (by decide +kernel) b3_1077
    · exact b3_784
    · exact b3_783
    · exact via sym3 fix3 (by decide +kernel) b3_191
    · exact b3_1075
    · exact via sym2 fix2 (by decide +kernel) b3_191
    · exact via sym1 fix1 (by decide +kernel) b3_1075
theorem b2_645 : Blocked tgt 8 s2_645 := by
  apply node_sound (nxt := [s3_1073,a1297,a1298,s3_747,s3_3,s3_1413,s3_1039,a1299,a1300,s3_1114,s3_1094,s3_759,s3_1101])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1073
    · exact via sym2 fix2 (by decide +kernel) b3_747
    · exact via sym2 fix2 (by decide +kernel) b3_1073
    · exact b3_747
    · exact b3_3
    · exact b3_1413
    · exact b3_1039
    · exact via sym2 fix2 (by decide +kernel) b3_1114
    · exact via sym2 fix2 (by decide +kernel) b3_1039
    · exact b3_1114
    · exact b3_1094
    · exact b3_759
    · exact b3_1101
theorem b2_646 : Blocked tgt 8 s2_646 := by
  apply node_sound (nxt := [s3_1048,a1301,s3_1192,s3_1404,s3_3,s3_1,s3_1544,s3_1101,a1302,s3_745,a1120,a1303,s3_1086,a1304,s3_1491,s3_1713,a1305,a1306,a1307,a1308,a1309,a1310,a1311,a1312,a1313,s3_110,a1314,a1315,s3_1088,s3_1038,a1316,s3_1098,a1317,s3_844,a1249,a1318,s3_1095,a1319,s3_1087,s3_1107,a1320,a1321,a1322,a1323,a1324,a1325,a1326,a1327,a1328,s3_260,a1329,a1330])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1048
    · exact via sym2 fix2 (by decide +kernel) b3_745
    · exact b3_1192
    · exact b3_1404
    · exact b3_3
    · exact b3_1
    · exact b3_1544
    · exact b3_1101
    · exact via sym2 fix2 (by decide +kernel) b3_1048
    · exact b3_745
    · exact via sym2 fix2 (by decide +kernel) b3_1192
    · exact via sym2 fix2 (by decide +kernel) b3_1404
    · exact b3_1086
    · exact via sym1 fix1 (by decide +kernel) b3_110
    · exact b3_1491
    · exact b3_1713
    · exact via sym2 fix2 (by decide +kernel) b3_1086
    · exact via sym3 fix3 (by decide +kernel) b3_110
    · exact via sym2 fix2 (by decide +kernel) b3_1491
    · exact via sym2 fix2 (by decide +kernel) b3_1713
    · exact via sym3 fix3 (by decide +kernel) b3_1086
    · exact via sym2 fix2 (by decide +kernel) b3_110
    · exact via sym3 fix3 (by decide +kernel) b3_1491
    · exact via sym3 fix3 (by decide +kernel) b3_1713
    · exact via sym1 fix1 (by decide +kernel) b3_1086
    · exact b3_110
    · exact via sym1 fix1 (by decide +kernel) b3_1491
    · exact via sym1 fix1 (by decide +kernel) b3_1713
    · exact b3_1088
    · exact b3_1038
    · exact via sym2 fix2 (by decide +kernel) b3_844
    · exact b3_1098
    · exact via sym2 fix2 (by decide +kernel) b3_1088
    · exact b3_844
    · exact via sym2 fix2 (by decide +kernel) b3_1038
    · exact via sym2 fix2 (by decide +kernel) b3_1098
    · exact b3_1095
    · exact via sym1 fix1 (by decide +kernel) b3_260
    · exact b3_1087
    · exact b3_1107
    · exact via sym2 fix2 (by decide +kernel) b3_1095
    · exact via sym3 fix3 (by decide +kernel) b3_260
    · exact via sym2 fix2 (by decide +kernel) b3_1087
    · exact via sym2 fix2 (by decide +kernel) b3_1107
    · exact via sym3 fix3 (by decide +kernel) b3_1095
    · exact via sym2 fix2 (by decide +kernel) b3_260
    · exact via sym3 fix3 (by decide +kernel) b3_1087
    · exact via sym3 fix3 (by decide +kernel) b3_1107
    · exact via sym1 fix1 (by decide +kernel) b3_1095
    · exact b3_260
    · exact via sym1 fix1 (by decide +kernel) b3_1087
    · exact via sym1 fix1 (by decide +kernel) b3_1107
theorem b2_647 : Blocked tgt 8 s2_647 := by
  apply node_sound (nxt := [s3_1039,a1331,a1300,s3_741,s3_1,s3_1426,s3_1417,s3_1094,a1332,s3_1090,s3_788,a1333,a1334,a1335,a1336,s3_193,a1337,s3_787,a1338,s3_1115,a1339,a1340,s3_1099,a1341,s3_762,s3_1109,a1342,a1343,a1344,a1345,a1346,a1347,a1348,a1349,a1350,s3_400,a1351,a1352])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1039
    · exact via sym2 fix2 (by decide +kernel) b3_741
    · exact via sym2 fix2 (by decide +kernel) b3_1039
    · exact b3_741
    · exact b3_1
    · exact b3_1426
    · exact b3_1417
    · exact b3_1094
    · exact via sym2 fix2 (by decide +kernel) b3_1090
    · exact b3_1090
    · exact b3_788
    · exact via sym2 fix2 (by decide +kernel) b3_788
    · exact via sym2 fix2 (by decide +kernel) b3_787
    · exact via sym1 fix1 (by decide +kernel) b3_193
    · exact via sym2 fix2 (by decide +kernel) b3_1115
    · exact b3_193
    · exact via sym3 fix3 (by decide +kernel) b3_1115
    · exact b3_787
    · exact via sym3 fix3 (by decide +kernel) b3_193
    · exact b3_1115
    · exact via sym2 fix2 (by decide +kernel) b3_193
    · exact via sym1 fix1 (by decide +kernel) b3_1115
    · exact b3_1099
    · exact via sym1 fix1 (by decide +kernel) b3_400
    · exact b3_762
    · exact b3_1109
    · exact via sym2 fix2 (by decide +kernel) b3_1099
    · exact via sym3 fix3 (by decide +kernel) b3_400
    · exact via sym2 fix2 (by decide +kernel) b3_762
    · exact via sym2 fix2 (by decide +kernel) b3_1109
    · exact via sym3 fix3 (by decide +kernel) b3_1099
    · exact via sym2 fix2 (by decide +kernel) b3_400
    · exact via sym3 fix3 (by decide +kernel) b3_762
    · exact via sym3 fix3 (by decide +kernel) b3_1109
    · exact via sym1 fix1 (by decide +kernel) b3_1099
    · exact b3_400
    · exact via sym1 fix1 (by decide +kernel) b3_762
    · exact via sym1 fix1 (by decide +kernel) b3_1109
end ThetaCert
