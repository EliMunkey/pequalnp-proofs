import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1464 : Blocked tgt 7 s3_1464 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1464 7 _ le
  decide +kernel
theorem b3_1465 : Blocked tgt 7 s3_1465 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1465 7 _ le
  decide +kernel
theorem b3_1466 : Blocked tgt 7 s3_1466 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(2,true))] s3_1466 7 _ le
  decide +kernel
theorem b3_1467 : Blocked tgt 7 s3_1467 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1467 7 _ le
  decide +kernel
theorem b3_1468 : Blocked tgt 7 s3_1468 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1468 7 _ le
  decide +kernel
theorem b3_1469 : Blocked tgt 7 s3_1469 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s3_1469 7 _ le
  decide +kernel
theorem b3_1470 : Blocked tgt 7 s3_1470 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1470 7 _ le
  decide +kernel
theorem b3_1471 : Blocked tgt 7 s3_1471 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1471 7 _ le
  decide +kernel
theorem b3_1472 : Blocked tgt 7 s3_1472 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1472 7 _ le
  decide +kernel
theorem b3_1473 : Blocked tgt 7 s3_1473 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1473 7 _ le
  decide +kernel
theorem b3_1474 : Blocked tgt 7 s3_1474 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1474 7 _ le
  decide +kernel
theorem b3_1475 : Blocked tgt 7 s3_1475 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1475 7 _ le
  decide +kernel
theorem b3_1476 : Blocked tgt 7 s3_1476 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1476 7 _ le
  decide +kernel
theorem b3_1477 : Blocked tgt 7 s3_1477 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1477 7 _ le
  decide +kernel
theorem b3_1478 : Blocked tgt 7 s3_1478 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1478 7 _ le
  decide +kernel
theorem b3_1479 : Blocked tgt 7 s3_1479 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_1479 7 _ le
  decide +kernel
theorem b3_1480 : Blocked tgt 7 s3_1480 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_1480 7 _ le
  decide +kernel
theorem b3_1481 : Blocked tgt 7 s3_1481 := by
  apply node_sound (nxt := [s4_49])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_49
theorem b3_1482 : Blocked tgt 7 s3_1482 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1482 7 _ le
  decide +kernel
theorem b3_1483 : Blocked tgt 7 s3_1483 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1484 : Blocked tgt 7 s3_1484 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_1484 7 _ le
  decide +kernel
theorem b3_1485 : Blocked tgt 7 s3_1485 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1486 : Blocked tgt 7 s3_1486 := by
  intro m le c
  apply rejects_sound extra156 i4 3 tgt small156 hot156 [] s3_1486 7 _ le
  decide +kernel
theorem b3_1487 : Blocked tgt 7 s3_1487 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_1487 7 _ le
  decide +kernel
end ThetaCert
