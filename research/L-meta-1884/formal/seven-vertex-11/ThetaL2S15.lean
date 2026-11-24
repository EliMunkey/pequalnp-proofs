import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S7
import ThetaL3S10
import ThetaL3S11
import ThetaL3S13
import ThetaL3S15
import ThetaL3S18
import ThetaL3S20
import ThetaL3S21
import ThetaL3S52
import ThetaL3S53
import ThetaL3S54
import ThetaL3S56
import ThetaL3S57
import ThetaL3S59
import ThetaL3S61
import ThetaL3S64
import ThetaL3S65
import ThetaL3S66
import ThetaL3S67
import ThetaL3S69
import ThetaL3S70
import ThetaL3S75
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_360 : Blocked tgt 8 s2_360 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s2_360 8 _ le
  decide +kernel
theorem b2_361 : Blocked tgt 8 s2_361 := by
  apply node_sound (nxt := [s3_171,s3_142,a980,s3_1366,s3_269,s3_111,a918,s3_1484,s3_331,s3_77,a981,a982,s3_445,s3_47,s3_1630,s3_1665,s3_492,s3_30,a983,a984,s3_493,s3_11,a985,a986,s3_3,a987,s3_505,s3_500,s3_497,s3_499,s3_506,s3_495,s3_508,a988,s3_509,a989,s3_510,s3_498,s3_503,s3_496,s3_507,s3_501,s3_494,a990,s3_504])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_171
    · exact b3_142
    · exact via sym1 fix1 (by decide +kernel) b3_1261
    · exact b3_1366
    · exact b3_269
    · exact b3_111
    · exact via sym1 fix1 (by decide +kernel) b3_1431
    · exact b3_1484
    · exact b3_331
    · exact b3_77
    · exact via sym3 fix3 (by decide +kernel) b3_1316
    · exact via sym2 fix2 (by decide +kernel) b3_1378
    · exact b3_445
    · exact b3_47
    · exact b3_1630
    · exact b3_1665
    · exact b3_492
    · exact b3_30
    · exact via sym1 fix1 (by decide +kernel) b3_1603
    · exact via sym2 fix2 (by decide +kernel) b3_1684
    · exact b3_493
    · exact b3_11
    · exact via sym1 fix1 (by decide +kernel) b3_1560
    · exact via sym3 fix3 (by decide +kernel) b3_1691
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1808
    · exact b3_505
    · exact b3_500
    · exact b3_497
    · exact b3_499
    · exact b3_506
    · exact b3_495
    · exact b3_508
    · exact via sym3 fix3 (by decide +kernel) b3_253
    · exact b3_509
    · exact via sym2 fix2 (by decide +kernel) b3_249
    · exact b3_510
    · exact b3_498
    · exact b3_503
    · exact b3_496
    · exact b3_507
    · exact b3_501
    · exact b3_494
    · exact via sym1 fix1 (by decide +kernel) b3_437
    · exact b3_504
theorem b2_362 : Blocked tgt 8 s2_362 := by
  intro m le c
  apply rejects_sound extra54 i5 4 tgt small54 hot54 [] s2_362 8 _ le
  decide +kernel
theorem b2_363 : Blocked tgt 8 s2_363 := by
  apply node_sound (nxt := [s3_172,s3_143,a991,s3_1367,s3_242,s3_115,a992,s3_1486,s3_362,s3_74,a954,a993,s3_445,s3_50,s3_1630,s3_1667,s3_512,s3_31,a994,a995,s3_513,s3_12,a996,a997,s3_3,a998,s3_522,s3_516,s3_519,s3_515,s3_520,a999,s3_521,s3_517,s3_514])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_172
    · exact b3_143
    · exact via sym1 fix1 (by decide +kernel) b3_1260
    · exact b3_1367
    · exact b3_242
    · exact b3_115
    · exact via sym1 fix1 (by decide +kernel) b3_1437
    · exact b3_1486
    · exact b3_362
    · exact b3_74
    · exact via sym3 fix3 (by decide +kernel) b3_1290
    · exact via sym2 fix2 (by decide +kernel) b3_1377
    · exact b3_445
    · exact b3_50
    · exact b3_1630
    · exact b3_1667
    · exact b3_512
    · exact b3_31
    · exact via sym1 fix1 (by decide +kernel) b3_1602
    · exact via sym2 fix2 (by decide +kernel) b3_1683
    · exact b3_513
    · exact b3_12
    · exact via sym1 fix1 (by decide +kernel) b3_1559
    · exact via sym3 fix3 (by decide +kernel) b3_1690
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1807
    · exact b3_522
    · exact b3_516
    · exact b3_519
    · exact b3_515
    · exact b3_520
    · exact via sym1 fix1 (by decide +kernel) b3_438
    · exact b3_521
    · exact b3_517
    · exact b3_514
theorem b2_364 : Blocked tgt 8 s2_364 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_364 8 _ le
  decide +kernel
theorem b2_365 : Blocked tgt 8 s2_365 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s2_365 8 _ le
  decide +kernel
theorem b2_366 : Blocked tgt 8 s2_366 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s2_366 8 _ le
  decide +kernel
theorem b2_367 : Blocked tgt 8 s2_367 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,true))] s2_367 8 _ le
  decide +kernel
theorem b2_368 : Blocked tgt 8 s2_368 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,false))] s2_368 8 _ le
  decide +kernel
theorem b2_369 : Blocked tgt 8 s2_369 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_369 8 _ le
  decide +kernel
theorem b2_370 : Blocked tgt 8 s2_370 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s2_370 8 _ le
  decide +kernel
theorem b2_371 : Blocked tgt 8 s2_371 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_371 8 _ le
  decide +kernel
theorem b2_372 : Blocked tgt 8 s2_372 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_372 8 _ le
  decide +kernel
theorem b2_373 : Blocked tgt 8 s2_373 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_373 8 _ le
  decide +kernel
theorem b2_374 : Blocked tgt 8 s2_374 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_374 8 _ le
  decide +kernel
theorem b2_375 : Blocked tgt 8 s2_375 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_375 8 _ le
  decide +kernel
theorem b2_376 : Blocked tgt 8 s2_376 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_376 8 _ le
  decide +kernel
theorem b2_377 : Blocked tgt 8 s2_377 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_377 8 _ le
  decide +kernel
theorem b2_378 : Blocked tgt 8 s2_378 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_378 8 _ le
  decide +kernel
theorem b2_379 : Blocked tgt 8 s2_379 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_379 8 _ le
  decide +kernel
theorem b2_380 : Blocked tgt 8 s2_380 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_380 8 _ le
  decide +kernel
theorem b2_381 : Blocked tgt 8 s2_381 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_381 8 _ le
  decide +kernel
theorem b2_382 : Blocked tgt 8 s2_382 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_382 8 _ le
  decide +kernel
theorem b2_383 : Blocked tgt 8 s2_383 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_383 8 _ le
  decide +kernel
end ThetaCert
