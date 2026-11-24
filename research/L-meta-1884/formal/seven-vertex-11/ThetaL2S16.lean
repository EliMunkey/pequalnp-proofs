import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S6
import ThetaL3S7
import ThetaL3S8
import ThetaL3S10
import ThetaL3S11
import ThetaL3S13
import ThetaL3S15
import ThetaL3S17
import ThetaL3S18
import ThetaL3S22
import ThetaL3S23
import ThetaL3S24
import ThetaL3S52
import ThetaL3S53
import ThetaL3S54
import ThetaL3S57
import ThetaL3S59
import ThetaL3S60
import ThetaL3S61
import ThetaL3S62
import ThetaL3S64
import ThetaL3S66
import ThetaL3S68
import ThetaL3S69
import ThetaL3S70
import ThetaL3S74
import ThetaL3S75
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_384 : Blocked tgt 8 s2_384 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_384 8 _ le
  decide +kernel
theorem b2_385 : Blocked tgt 8 s2_385 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_385 8 _ le
  decide +kernel
theorem b2_386 : Blocked tgt 8 s2_386 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_386 8 _ le
  decide +kernel
theorem b2_387 : Blocked tgt 8 s2_387 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_387 8 _ le
  decide +kernel
theorem b2_388 : Blocked tgt 8 s2_388 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_388 8 _ le
  decide +kernel
theorem b2_389 : Blocked tgt 8 s2_389 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_389 8 _ le
  decide +kernel
theorem b2_390 : Blocked tgt 8 s2_390 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_390 8 _ le
  decide +kernel
theorem b2_391 : Blocked tgt 8 s2_391 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_391 8 _ le
  decide +kernel
theorem b2_392 : Blocked tgt 8 s2_392 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s2_392 8 _ le
  decide +kernel
theorem b2_393 : Blocked tgt 8 s2_393 := by
  apply node_sound (nxt := [s3_199,s3_145,a917,s3_1368,s3_245,s3_119,a1000,s3_1488,s3_334,s3_79,a1001,a1002,s3_427,s3_56,s3_1635,s3_1672,s3_536,s3_20,a1003,a1004,s3_562,a1005,a1006,a1007,s3_3,a1008,s3_567,s3_563,s3_565,a1009,s3_568,a1010,s3_566])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_199
    · exact b3_145
    · exact via sym1 fix1 (by decide +kernel) b3_1250
    · exact b3_1368
    · exact b3_245
    · exact b3_119
    · exact via sym1 fix1 (by decide +kernel) b3_1447
    · exact b3_1488
    · exact b3_334
    · exact b3_79
    · exact via sym3 fix3 (by decide +kernel) b3_1307
    · exact via sym2 fix2 (by decide +kernel) b3_1376
    · exact b3_427
    · exact b3_56
    · exact b3_1635
    · exact b3_1672
    · exact b3_536
    · exact b3_20
    · exact via sym1 fix1 (by decide +kernel) b3_1599
    · exact via sym2 fix2 (by decide +kernel) b3_1679
    · exact b3_562
    · exact via sym2 fix2 (by decide +kernel) b3_12
    · exact via sym3 fix3 (by decide +kernel) b3_1551
    · exact via sym3 fix3 (by decide +kernel) b3_1695
    · exact b3_3
    · exact via sym1 fix1 (by decide +kernel) b3_1795
    · exact b3_567
    · exact b3_563
    · exact b3_565
    · exact via sym2 fix2 (by decide +kernel) b3_432
    · exact b3_568
    · exact via sym3 fix3 (by decide +kernel) b3_530
    · exact b3_566
theorem b2_394 : Blocked tgt 8 s2_394 := by
  intro m le c
  apply rejects_sound extra44 i5 4 tgt small44 hot44 [] s2_394 8 _ le
  decide +kernel
theorem b2_395 : Blocked tgt 8 s2_395 := by
  apply node_sound (nxt := [s3_175,s3_147,a1011,s3_1369,s3_269,s3_116,a918,s3_1487,s3_335,s3_80,a1012,a1013,s3_428,s3_57,s3_1634,s3_1673,s3_536,s3_25,a1003,a1014,s3_569,a1015,a1016,a1017,s3_572,a1018,a1019,s3_577,s3_3,a1020,s3_576,s3_571,s3_574,s3_570,s3_578,a1021,s3_575])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_175
    · exact b3_147
    · exact via sym1 fix1 (by decide +kernel) b3_1269
    · exact b3_1369
    · exact b3_269
    · exact b3_116
    · exact via sym1 fix1 (by decide +kernel) b3_1431
    · exact b3_1487
    · exact b3_335
    · exact b3_80
    · exact via sym3 fix3 (by decide +kernel) b3_1308
    · exact via sym2 fix2 (by decide +kernel) b3_1375
    · exact b3_428
    · exact b3_57
    · exact b3_1634
    · exact b3_1673
    · exact b3_536
    · exact b3_25
    · exact via sym1 fix1 (by decide +kernel) b3_1599
    · exact via sym2 fix2 (by decide +kernel) b3_1677
    · exact b3_569
    · exact via sym2 fix2 (by decide +kernel) b3_11
    · exact via sym3 fix3 (by decide +kernel) b3_1553
    · exact via sym3 fix3 (by decide +kernel) b3_1552
    · exact b3_572
    · exact via sym2 fix2 (by decide +kernel) b3_1816
    · exact via sym3 fix3 (by decide +kernel) b3_1694
    · exact b3_577
    · exact b3_3
    · exact via sym1 fix1 (by decide +kernel) b3_1796
    · exact b3_576
    · exact b3_571
    · exact b3_574
    · exact b3_570
    · exact b3_578
    · exact via sym3 fix3 (by decide +kernel) b3_529
    · exact b3_575
theorem b2_396 : Blocked tgt 8 s2_396 := by
  intro m le c
  apply rejects_sound extra57 i4 3 tgt small57 hot57 [] s2_396 8 _ le
  decide +kernel
theorem b2_397 : Blocked tgt 8 s2_397 := by
  apply node_sound (nxt := [s3_176,s3_148,a1022,s3_1370,s3_246,s3_120,a1023,s3_1489,s3_362,s3_78,a954,a1024,s3_429,s3_59,s3_1633,s3_1674,s3_536,a1025,a1003,a1026,s3_581,a1027,a1028,a1029,s3_3,a1030,s3_591,s3_585,s3_588,s3_584,s3_589,a1031,s3_593,a1032,s3_590,s3_586,s3_582])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_176
    · exact b3_148
    · exact via sym1 fix1 (by decide +kernel) b3_1268
    · exact b3_1370
    · exact b3_246
    · exact b3_120
    · exact via sym1 fix1 (by decide +kernel) b3_1446
    · exact b3_1489
    · exact b3_362
    · exact b3_78
    · exact via sym3 fix3 (by decide +kernel) b3_1290
    · exact via sym2 fix2 (by decide +kernel) b3_1374
    · exact b3_429
    · exact b3_59
    · exact b3_1633
    · exact b3_1674
    · exact b3_536
    · exact via sym3 fix3 (by decide +kernel) b3_20
    · exact via sym1 fix1 (by decide +kernel) b3_1599
    · exact via sym2 fix2 (by decide +kernel) b3_1675
    · exact b3_581
    · exact via sym2 fix2 (by decide +kernel) b3_10
    · exact via sym3 fix3 (by decide +kernel) b3_1554
    · exact via sym3 fix3 (by decide +kernel) b3_1693
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1795
    · exact b3_591
    · exact b3_585
    · exact b3_588
    · exact b3_584
    · exact b3_589
    · exact via sym2 fix2 (by decide +kernel) b3_431
    · exact b3_593
    · exact via sym3 fix3 (by decide +kernel) b3_528
    · exact b3_590
    · exact b3_586
    · exact b3_582
theorem b2_398 : Blocked tgt 8 s2_398 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s2_398 8 _ le
  decide +kernel
theorem b2_399 : Blocked tgt 8 s2_399 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s2_399 8 _ le
  decide +kernel
theorem b2_400 : Blocked tgt 8 s2_400 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(1,true))] s2_400 8 _ le
  decide +kernel
theorem b2_401 : Blocked tgt 8 s2_401 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,true))] s2_401 8 _ le
  decide +kernel
theorem b2_402 : Blocked tgt 8 s2_402 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,false))] s2_402 8 _ le
  decide +kernel
theorem b2_403 : Blocked tgt 8 s2_403 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_403 8 _ le
  decide +kernel
theorem b2_404 : Blocked tgt 8 s2_404 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s2_404 8 _ le
  decide +kernel
theorem b2_405 : Blocked tgt 8 s2_405 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s2_405 8 _ le
  decide +kernel
theorem b2_406 : Blocked tgt 8 s2_406 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s2_406 8 _ le
  decide +kernel
theorem b2_407 : Blocked tgt 8 s2_407 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s2_407 8 _ le
  decide +kernel
end ThetaCert
