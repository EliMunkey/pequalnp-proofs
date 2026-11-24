import Q1020K12L2S6Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S13
import Q1020K12L3S15
import Q1020K12L3S17
import Q1020K12L3S18
import Q1020K12L3S27
import Q1020K12L3S30
import Q1020K12L3S31
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S57
import Q1020K12L3S62
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S71
import Q1020K12L3S72
import Q1020K12L3S73
import Q1020K12L3S77
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S6Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_274 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_274 := by
  apply PetersenIndexedNode.close (bank := [s3_400,a1265,a1266,s3_2722,s3_578,a1267,a1268,a1269,s3_1361,a1270,s3_3022,a1271,s3_1154,a1272,a1273,a1274,a1275,s3_345,a1276,a1277,a1278,s3_304,a1279,a1280,a1281,a1282,s3_1389,a1283,a1284,a1285,a1286,a1071,s3_1432,s3_574,s3_561,a825,a826,a1287,a1288,s3_1416,a807,a1289,s3_1425,a1290,s3_1428,s3_1334,a1291,a1292,s3_1420,a1293,a1294,s3_1296,a1295,a1296,a1297,s3_1359,s3_1358,s3_633,a1298,s3_4,a1299,a1300,s3_1447,a1301,s3_1431,s3_1379,s3_1380,s3_1378,a1302,a1303,a1304,a1305,s3_1421,a1306,a1307,s3_1314,s3_1422,s3_1299,a1308,a1309,a1310,a1311,a1312,s3_1304,s3_1423,a1313,s3_1290,s3_1393,s3_1394,s3_1392,s3_1292,s3_1293,s3_1291,a1314,s3_1433,a1315,a1316,s3_1282,s3_1426,s3_632]) (PetersenIndexedNode.reasons 256 17 510 0x200c700394202400ed242484048030920209011006021011080a00c4420221014017c90104808802e908088404921261413080a00bcc28221412484884044202802e4016e00b500245040282020054a08050404016600b10057802b40155440500205040282012425001a49091888941006222210138300840462227060188888404a08021014014ca08050408029242012101005448402420200a25040282024848a08092028028242012404921248402484a009e504028201404121005000210114100a000501028201404084049080210140134a080504050401c180e0c1004e38301c1814100504028204012c5040282080250a8885445004c15110a88a0092282014102686850409a1249093230124249a1a6460248692424282049091202050404800210112100900048082420120208404282021012a2209080484050400a0805040a88814100a081410048402420262205040282028200e0c0704098881c180a0c0a080282014104011e008d00458022018080c05004803010180a008700428020c00fc0c0406024909212010c050040424021201242406020301130300c04060221013130084044c0c626012030840406020301400f40c0406025040098884c45003e131109889410006020301151100c0406022820058482c0454440b0901848a080060203010b0900c0406021410038281c042c24070501828504006020301400f200740301801da0e0406029212801d2484a0072838141c0c00e2006e9012210120e04840448086160120208404c2c021011202107024808514120e054500a080801aa8201450500365041282010702a080494120e05250050408019941012505003448411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808018a12000c050032030121201070284808017884804241002e018100c0a006003020181400b442402120801580c080604921241c120c0a0058838201c12484806040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208013c009a004b00248002c008e0055002980144008a0009002180104007d44449212800c24848c445001d31111080a00384202311140078c4444202800d9080a003500191080a820200302101383040058e0c05040800a94100e0c10017383014102002850401410400485040484080089210050410013141012102002048401311400384c4406028006818084c45000f13110180a0018060280044001e000c83818002a0e060017000a8004a0e060008838110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_400 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_346 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2639 theta)
    · exact b3_2722 theta
    · exact b3_578 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_134 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2848 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2844 theta)
    · exact b3_1361 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_3360 theta)
    · exact b3_3022 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1436 theta)
    · exact b3_1154 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_305 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2432 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2747 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_401 theta)
    · exact b3_345 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2641 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2723 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1155 theta)
    · exact b3_304 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2433 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2749 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_18 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2883 theta)
    · exact b3_1389 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_580 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_128 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2846 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3028 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3273 theta)
    · exact b3_1432 theta
    · exact b3_574 theta
    · exact b3_561 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_129 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_80 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3096 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3085 theta)
    · exact b3_1416 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3281 theta)
    · exact b3_1425 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1313 theta)
    · exact b3_1428 theta
    · exact b3_1334 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_157 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1315 theta)
    · exact b3_1420 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1301 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1440 theta)
    · exact b3_1296 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1439 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_722 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1442 theta)
    · exact b3_1359 theta
    · exact b3_1358 theta
    · exact b3_633 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_790 theta)
    · exact b3_4 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_789 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1300 theta)
    · exact b3_1447 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1303 theta)
    · exact b3_1431 theta
    · exact b3_1379 theta
    · exact b3_1380 theta
    · exact b3_1378 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_182 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1306 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1307 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1305 theta)
    · exact b3_1421 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1335 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_47 theta)
    · exact b3_1314 theta
    · exact b3_1422 theta
    · exact b3_1299 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1448 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1374 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1169 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1381 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_156 theta)
    · exact b3_1304 theta
    · exact b3_1423 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1288 theta)
    · exact b3_1290 theta
    · exact b3_1393 theta
    · exact b3_1394 theta
    · exact b3_1392 theta
    · exact b3_1292 theta
    · exact b3_1293 theta
    · exact b3_1291 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_791 theta)
    · exact b3_1433 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1364 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_76 theta)
    · exact b3_1282 theta
    · exact b3_1426 theta
    · exact b3_632 theta
theorem b2_275 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_275 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s2_275 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w76 rfl)))))))))) (by decide +kernel)
theorem b2_276 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_276 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_276 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc2w11 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w77 rfl)))))))))) (by decide +kernel)
theorem b2_277 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_277 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_277 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w11 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w77 rfl))))))))) (by decide +kernel)
theorem b2_278 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_278 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s2_278 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w38 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
