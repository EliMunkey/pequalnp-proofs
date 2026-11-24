import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_384 : Blocked tgt 7 s3_384 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_384 7 _ le
  decide +kernel
theorem b3_385 : Blocked tgt 7 s3_385 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_385 7 _ le
  decide +kernel
theorem b3_386 : Blocked tgt 7 s3_386 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_386 7 _ le
  decide +kernel
theorem b3_387 : Blocked tgt 7 s3_387 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_387 7 _ le
  decide +kernel
theorem b3_388 : Blocked tgt 7 s3_388 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_388 7 _ le
  decide +kernel
theorem b3_389 : Blocked tgt 7 s3_389 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_389 7 _ le
  decide +kernel
theorem b3_390 : Blocked tgt 7 s3_390 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_390 7 _ le
  decide +kernel
theorem b3_391 : Blocked tgt 7 s3_391 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_391 7 _ le
  decide +kernel
theorem b3_392 : Blocked tgt 7 s3_392 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_392 7 _ le
  decide +kernel
theorem b3_393 : Blocked tgt 7 s3_393 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s3_393 7 _ le
  decide +kernel
theorem b3_394 : Blocked tgt 7 s3_394 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_394 7 _ le
  decide +kernel
theorem b3_395 : Blocked tgt 7 s3_395 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_395 7 _ le
  decide +kernel
theorem b3_396 : Blocked tgt 7 s3_396 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_396 7 _ le
  decide +kernel
theorem b3_397 : Blocked tgt 7 s3_397 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_397 7 _ le
  decide +kernel
theorem b3_398 : Blocked tgt 7 s3_398 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_398 7 _ le
  decide +kernel
theorem b3_399 : Blocked tgt 7 s3_399 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_399 7 _ le
  decide +kernel
theorem b3_400 : Blocked tgt 7 s3_400 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_401 : Blocked tgt 7 s3_401 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_401 7 _ le
  decide +kernel
theorem b3_402 : Blocked tgt 7 s3_402 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_403 : Blocked tgt 7 s3_403 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_403 7 _ le
  decide +kernel
theorem b3_404 : Blocked tgt 7 s3_404 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_404 7 _ le
  decide +kernel
theorem b3_405 : Blocked tgt 7 s3_405 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_405 7 _ le
  decide +kernel
theorem b3_406 : Blocked tgt 7 s3_406 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_406 7 _ le
  decide +kernel
theorem b3_407 : Blocked tgt 7 s3_407 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_407 7 _ le
  decide +kernel
end ThetaCert
