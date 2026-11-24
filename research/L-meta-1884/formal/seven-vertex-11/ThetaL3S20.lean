import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_480 : Blocked tgt 7 s3_480 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_480 7 _ le
  decide +kernel
theorem b3_481 : Blocked tgt 7 s3_481 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_481 7 _ le
  decide +kernel
theorem b3_482 : Blocked tgt 7 s3_482 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_482 7 _ le
  decide +kernel
theorem b3_483 : Blocked tgt 7 s3_483 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_483 7 _ le
  decide +kernel
theorem b3_484 : Blocked tgt 7 s3_484 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_484 7 _ le
  decide +kernel
theorem b3_485 : Blocked tgt 7 s3_485 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_485 7 _ le
  decide +kernel
theorem b3_486 : Blocked tgt 7 s3_486 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_486 7 _ le
  decide +kernel
theorem b3_487 : Blocked tgt 7 s3_487 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s3_487 7 _ le
  decide +kernel
theorem b3_488 : Blocked tgt 7 s3_488 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_488 7 _ le
  decide +kernel
theorem b3_489 : Blocked tgt 7 s3_489 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_489 7 _ le
  decide +kernel
theorem b3_490 : Blocked tgt 7 s3_490 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_490 7 _ le
  decide +kernel
theorem b3_491 : Blocked tgt 7 s3_491 := by
  intro m le c
  apply rejects_sound extra66 i5 4 tgt small66 hot66 [] s3_491 7 _ le
  decide +kernel
theorem b3_492 : Blocked tgt 7 s3_492 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_492 7 _ le
  decide +kernel
theorem b3_493 : Blocked tgt 7 s3_493 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_493 7 _ le
  decide +kernel
theorem b3_494 : Blocked tgt 7 s3_494 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_494 7 _ le
  decide +kernel
theorem b3_495 : Blocked tgt 7 s3_495 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,false),(5,true))] s3_495 7 _ le
  decide +kernel
theorem b3_496 : Blocked tgt 7 s3_496 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_496 7 _ le
  decide +kernel
theorem b3_497 : Blocked tgt 7 s3_497 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_498 : Blocked tgt 7 s3_498 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_498 7 _ le
  decide +kernel
theorem b3_499 : Blocked tgt 7 s3_499 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_499 7 _ le
  decide +kernel
theorem b3_500 : Blocked tgt 7 s3_500 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,false),(5,true))] s3_500 7 _ le
  decide +kernel
theorem b3_501 : Blocked tgt 7 s3_501 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_501 7 _ le
  decide +kernel
theorem b3_502 : Blocked tgt 7 s3_502 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_502 7 _ le
  decide +kernel
theorem b3_503 : Blocked tgt 7 s3_503 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,false),(5,true))] s3_503 7 _ le
  decide +kernel
end ThetaCert
