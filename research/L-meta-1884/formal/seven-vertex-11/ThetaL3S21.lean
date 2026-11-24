import ThetaAlias
import ThetaL4S0
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_504 : Blocked tgt 7 s3_504 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_504 7 _ le
  decide +kernel
theorem b3_505 : Blocked tgt 7 s3_505 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_505 7 _ le
  decide +kernel
theorem b3_506 : Blocked tgt 7 s3_506 := by
  apply node_sound (nxt := [s4_0])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_0
theorem b3_507 : Blocked tgt 7 s3_507 := by
  intro m le c
  apply rejects_sound extra66 i5 4 tgt small66 hot66 [] s3_507 7 _ le
  decide +kernel
theorem b3_508 : Blocked tgt 7 s3_508 := by
  intro m le c
  apply rejects_sound extra66 i5 4 tgt small66 hot66 [] s3_508 7 _ le
  decide +kernel
theorem b3_509 : Blocked tgt 7 s3_509 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_509 7 _ le
  decide +kernel
theorem b3_510 : Blocked tgt 7 s3_510 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_510 7 _ le
  decide +kernel
theorem b3_511 : Blocked tgt 7 s3_511 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_511 7 _ le
  decide +kernel
theorem b3_512 : Blocked tgt 7 s3_512 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_512 7 _ le
  decide +kernel
theorem b3_513 : Blocked tgt 7 s3_513 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_513 7 _ le
  decide +kernel
theorem b3_514 : Blocked tgt 7 s3_514 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_514 7 _ le
  decide +kernel
theorem b3_515 : Blocked tgt 7 s3_515 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_515 7 _ le
  decide +kernel
theorem b3_516 : Blocked tgt 7 s3_516 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_516 7 _ le
  decide +kernel
theorem b3_517 : Blocked tgt 7 s3_517 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_517 7 _ le
  decide +kernel
theorem b3_518 : Blocked tgt 7 s3_518 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_518 7 _ le
  decide +kernel
theorem b3_519 : Blocked tgt 7 s3_519 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_519 7 _ le
  decide +kernel
theorem b3_520 : Blocked tgt 7 s3_520 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_520 7 _ le
  decide +kernel
theorem b3_521 : Blocked tgt 7 s3_521 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s3_521 7 _ le
  decide +kernel
theorem b3_522 : Blocked tgt 7 s3_522 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_522 7 _ le
  decide +kernel
theorem b3_523 : Blocked tgt 7 s3_523 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_523 7 _ le
  decide +kernel
theorem b3_524 : Blocked tgt 7 s3_524 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_524 7 _ le
  decide +kernel
theorem b3_525 : Blocked tgt 7 s3_525 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_525 7 _ le
  decide +kernel
theorem b3_526 : Blocked tgt 7 s3_526 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_526 7 _ le
  decide +kernel
theorem b3_527 : Blocked tgt 7 s3_527 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_527 7 _ le
  decide +kernel
end ThetaCert
