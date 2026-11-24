import ThetaAlias
import ThetaL3S0
import ThetaL3S30
import ThetaL3S31
import ThetaL3S63
import ThetaL3S64
import ThetaL3S79
import ThetaL3S80
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_432 : Blocked tgt 8 s2_432 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_432 8 _ le
  decide +kernel
theorem b2_433 : Blocked tgt 8 s2_433 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_433 8 _ le
  decide +kernel
theorem b2_434 : Blocked tgt 8 s2_434 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_434 8 _ le
  decide +kernel
theorem b2_435 : Blocked tgt 8 s2_435 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_435 8 _ le
  decide +kernel
theorem b2_436 : Blocked tgt 8 s2_436 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_436 8 _ le
  decide +kernel
theorem b2_437 : Blocked tgt 8 s2_437 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_437 8 _ le
  decide +kernel
theorem b2_438 : Blocked tgt 8 s2_438 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_438 8 _ le
  decide +kernel
theorem b2_439 : Blocked tgt 8 s2_439 := by
  apply node_sound (nxt := [s3_1932,s3_1896,s3_3,s3_1544,a1064,a1065,a1066,a1067,s3_744,s3_743,s3_739])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1932
    · exact b3_1896
    · exact b3_3
    · exact b3_1544
    · exact via sym2 fix2 (by decide +kernel) b3_1520
    · exact via sym3 fix3 (by decide +kernel) b3_1526
    · exact via sym3 fix3 (by decide +kernel) b3_1520
    · exact via sym2 fix2 (by decide +kernel) b3_1526
    · exact b3_744
    · exact b3_743
    · exact b3_739
theorem b2_440 : Blocked tgt 8 s2_440 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_440 8 _ le
  decide +kernel
theorem b2_441 : Blocked tgt 8 s2_441 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_441 8 _ le
  decide +kernel
theorem b2_442 : Blocked tgt 8 s2_442 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_442 8 _ le
  decide +kernel
theorem b2_443 : Blocked tgt 8 s2_443 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s2_443 8 _ le
  decide +kernel
theorem b2_444 : Blocked tgt 8 s2_444 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_444 8 _ le
  decide +kernel
theorem b2_445 : Blocked tgt 8 s2_445 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s2_445 8 _ le
  decide +kernel
theorem b2_446 : Blocked tgt 8 s2_446 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_446 8 _ le
  decide +kernel
theorem b2_447 : Blocked tgt 8 s2_447 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_447 8 _ le
  decide +kernel
theorem b2_448 : Blocked tgt 8 s2_448 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_448 8 _ le
  decide +kernel
theorem b2_449 : Blocked tgt 8 s2_449 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_449 8 _ le
  decide +kernel
theorem b2_450 : Blocked tgt 8 s2_450 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_450 8 _ le
  decide +kernel
theorem b2_451 : Blocked tgt 8 s2_451 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_451 8 _ le
  decide +kernel
theorem b2_452 : Blocked tgt 8 s2_452 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_452 8 _ le
  decide +kernel
theorem b2_453 : Blocked tgt 8 s2_453 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s2_453 8 _ le
  decide +kernel
theorem b2_454 : Blocked tgt 8 s2_454 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_454 8 _ le
  decide +kernel
theorem b2_455 : Blocked tgt 8 s2_455 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,false),(1,true))] s2_455 8 _ le
  decide +kernel
end ThetaCert
