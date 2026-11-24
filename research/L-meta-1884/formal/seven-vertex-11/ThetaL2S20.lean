import ThetaAlias
import ThetaL3S1
import ThetaL3S2
import ThetaL3S3
import ThetaL3S31
import ThetaL3S32
import ThetaL3S33
import ThetaL3S34
import ThetaL3S51
import ThetaL3S57
import ThetaL3S58
import ThetaL3S63
import ThetaL3S64
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S76
import ThetaL3S79
import ThetaL3S80
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_480 : Blocked tgt 8 s2_480 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_480 8 _ le
  decide +kernel
theorem b2_481 : Blocked tgt 8 s2_481 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_481 8 _ le
  decide +kernel
theorem b2_482 : Blocked tgt 8 s2_482 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_482 8 _ le
  decide +kernel
theorem b2_483 : Blocked tgt 8 s2_483 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_483 8 _ le
  decide +kernel
theorem b2_484 : Blocked tgt 8 s2_484 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_484 8 _ le
  decide +kernel
theorem b2_485 : Blocked tgt 8 s2_485 := by
  apply node_sound (nxt := [a1068,s3_1932,s3_1907,s3_771,s3_745,a1069,s3_1544,a1070,a1071,a1072,a1073,s3_795,s3_791])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1227
    · exact b3_1932
    · exact b3_1907
    · exact b3_771
    · exact b3_745
    · exact via sym2 fix2 (by decide +kernel) b3_1383
    · exact b3_1544
    · exact via sym2 fix2 (by decide +kernel) b3_1386
    · exact via sym3 fix3 (by decide +kernel) b3_1527
    · exact via sym3 fix3 (by decide +kernel) b3_1386
    · exact via sym2 fix2 (by decide +kernel) b3_1527
    · exact b3_795
    · exact b3_791
theorem b2_486 : Blocked tgt 8 s2_486 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_486 8 _ le
  decide +kernel
theorem b2_487 : Blocked tgt 8 s2_487 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s2_487 8 _ le
  decide +kernel
theorem b2_488 : Blocked tgt 8 s2_488 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s2_488 8 _ le
  decide +kernel
theorem b2_489 : Blocked tgt 8 s2_489 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_489 8 _ le
  decide +kernel
theorem b2_490 : Blocked tgt 8 s2_490 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_490 8 _ le
  decide +kernel
theorem b2_491 : Blocked tgt 8 s2_491 := by
  apply node_sound (nxt := [s3_772,s3_749,a1074,a1075,s3_776,a1076,a1077,s3_1764,a1078,s3_1755,s3_786,a1079,a1080,s3_827])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_772
    · exact b3_749
    · exact via sym2 fix2 (by decide +kernel) b3_1388
    · exact via sym1 fix1 (by decide +kernel) b3_1832
    · exact b3_776
    · exact via sym1 fix1 (by decide +kernel) b3_60
    · exact via sym2 fix2 (by decide +kernel) b3_1394
    · exact b3_1764
    · exact via sym3 fix3 (by decide +kernel) b3_1390
    · exact b3_1755
    · exact b3_786
    · exact via sym1 fix1 (by decide +kernel) b3_830
    · exact via sym1 fix1 (by decide +kernel) b3_94
    · exact b3_827
theorem b2_492 : Blocked tgt 8 s2_492 := by
  apply node_sound (nxt := [a1081,a1082,s3_774,a1083,a1084,s3_1778,a1085,s3_1771,s3_796,s3_792])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1387
    · exact via sym1 fix1 (by decide +kernel) b3_1834
    · exact b3_774
    · exact via sym1 fix1 (by decide +kernel) b3_68
    · exact via sym2 fix2 (by decide +kernel) b3_1396
    · exact b3_1778
    · exact via sym3 fix3 (by decide +kernel) b3_1389
    · exact b3_1771
    · exact b3_796
    · exact b3_792
theorem b2_493 : Blocked tgt 8 s2_493 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s2_493 8 _ le
  decide +kernel
theorem b2_494 : Blocked tgt 8 s2_494 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_494 8 _ le
  decide +kernel
theorem b2_495 : Blocked tgt 8 s2_495 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_495 8 _ le
  decide +kernel
theorem b2_496 : Blocked tgt 8 s2_496 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_496 8 _ le
  decide +kernel
theorem b2_497 : Blocked tgt 8 s2_497 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_497 8 _ le
  decide +kernel
theorem b2_498 : Blocked tgt 8 s2_498 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_498 8 _ le
  decide +kernel
theorem b2_499 : Blocked tgt 8 s2_499 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s2_499 8 _ le
  decide +kernel
theorem b2_500 : Blocked tgt 8 s2_500 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_500 8 _ le
  decide +kernel
theorem b2_501 : Blocked tgt 8 s2_501 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_501 8 _ le
  decide +kernel
theorem b2_502 : Blocked tgt 8 s2_502 := by
  apply node_sound (nxt := [a1086,a1087,a1088,s3_1836,s3_781,s3_32,a1089,a1090,a1091,s3_831,s3_41,s3_828])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1391
    · exact via sym1 fix1 (by decide +kernel) b3_1836
    · exact via sym3 fix3 (by decide +kernel) b3_1391
    · exact b3_1836
    · exact b3_781
    · exact b3_32
    · exact via sym2 fix2 (by decide +kernel) b3_1399
    · exact via sym2 fix2 (by decide +kernel) b3_1805
    · exact via sym1 fix1 (by decide +kernel) b3_831
    · exact b3_831
    · exact b3_41
    · exact b3_828
theorem b2_503 : Blocked tgt 8 s2_503 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_503 8 _ le
  decide +kernel
end ThetaCert
