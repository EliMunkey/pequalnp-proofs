import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S8
import ThetaL3S10
import ThetaL3S13
import ThetaL3S18
import ThetaL3S19
import ThetaL3S20
import ThetaL3S52
import ThetaL3S54
import ThetaL3S56
import ThetaL3S57
import ThetaL3S59
import ThetaL3S61
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
theorem b2_336 : Blocked tgt 8 s2_336 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_336 8 _ le
  decide +kernel
theorem b2_337 : Blocked tgt 8 s2_337 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_337 8 _ le
  decide +kernel
theorem b2_338 : Blocked tgt 8 s2_338 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_338 8 _ le
  decide +kernel
theorem b2_339 : Blocked tgt 8 s2_339 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_339 8 _ le
  decide +kernel
theorem b2_340 : Blocked tgt 8 s2_340 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_340 8 _ le
  decide +kernel
theorem b2_341 : Blocked tgt 8 s2_341 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_341 8 _ le
  decide +kernel
theorem b2_342 : Blocked tgt 8 s2_342 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_342 8 _ le
  decide +kernel
theorem b2_343 : Blocked tgt 8 s2_343 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_343 8 _ le
  decide +kernel
theorem b2_344 : Blocked tgt 8 s2_344 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_344 8 _ le
  decide +kernel
theorem b2_345 : Blocked tgt 8 s2_345 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_345 8 _ le
  decide +kernel
theorem b2_346 : Blocked tgt 8 s2_346 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_346 8 _ le
  decide +kernel
theorem b2_347 : Blocked tgt 8 s2_347 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_347 8 _ le
  decide +kernel
theorem b2_348 : Blocked tgt 8 s2_348 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_348 8 _ le
  decide +kernel
theorem b2_349 : Blocked tgt 8 s2_349 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_349 8 _ le
  decide +kernel
theorem b2_350 : Blocked tgt 8 s2_350 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_350 8 _ le
  decide +kernel
theorem b2_351 : Blocked tgt 8 s2_351 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_351 8 _ le
  decide +kernel
theorem b2_352 : Blocked tgt 8 s2_352 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_352 8 _ le
  decide +kernel
theorem b2_353 : Blocked tgt 8 s2_353 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_353 8 _ le
  decide +kernel
theorem b2_354 : Blocked tgt 8 s2_354 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_354 8 _ le
  decide +kernel
theorem b2_355 : Blocked tgt 8 s2_355 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_355 8 _ le
  decide +kernel
theorem b2_356 : Blocked tgt 8 s2_356 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_356 8 _ le
  decide +kernel
theorem b2_357 : Blocked tgt 8 s2_357 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_357 8 _ le
  decide +kernel
theorem b2_358 : Blocked tgt 8 s2_358 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s2_358 8 _ le
  decide +kernel
theorem b2_359 : Blocked tgt 8 s2_359 := by
  apply node_sound (nxt := [s3_199,s3_140,a917,s3_1365,s3_241,s3_114,a971,s3_1485,s3_330,s3_76,a972,a973,s3_445,s3_42,s3_1630,s3_1663,s3_479,s3_29,a974,a975,s3_480,s3_10,a976,a977,s3_3,a978,s3_488,s3_483,s3_491,s3_484,s3_486,s3_481,s3_490,a979,s3_487])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_199
    · exact b3_140
    · exact via sym1 fix1 (by decide +kernel) b3_1250
    · exact b3_1365
    · exact b3_241
    · exact b3_114
    · exact via sym1 fix1 (by decide +kernel) b3_1438
    · exact b3_1485
    · exact b3_330
    · exact b3_76
    · exact via sym3 fix3 (by decide +kernel) b3_1315
    · exact via sym2 fix2 (by decide +kernel) b3_1379
    · exact b3_445
    · exact b3_42
    · exact b3_1630
    · exact b3_1663
    · exact b3_479
    · exact b3_29
    · exact via sym1 fix1 (by decide +kernel) b3_1604
    · exact via sym2 fix2 (by decide +kernel) b3_1685
    · exact b3_480
    · exact b3_10
    · exact via sym1 fix1 (by decide +kernel) b3_1561
    · exact via sym3 fix3 (by decide +kernel) b3_1692
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1810
    · exact b3_488
    · exact b3_483
    · exact b3_491
    · exact b3_484
    · exact b3_486
    · exact b3_481
    · exact b3_490
    · exact via sym1 fix1 (by decide +kernel) b3_436
    · exact b3_487
end ThetaCert
