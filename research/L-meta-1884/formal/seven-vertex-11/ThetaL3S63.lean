import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1512 : Blocked tgt 7 s3_1512 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1512 7 _ le
  decide +kernel
theorem b3_1513 : Blocked tgt 7 s3_1513 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1513 7 _ le
  decide +kernel
theorem b3_1514 : Blocked tgt 7 s3_1514 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1514 7 _ le
  decide +kernel
theorem b3_1515 : Blocked tgt 7 s3_1515 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1515 7 _ le
  decide +kernel
theorem b3_1516 : Blocked tgt 7 s3_1516 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1516 7 _ le
  decide +kernel
theorem b3_1517 : Blocked tgt 7 s3_1517 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1517 7 _ le
  decide +kernel
theorem b3_1518 : Blocked tgt 7 s3_1518 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1518 7 _ le
  decide +kernel
theorem b3_1519 : Blocked tgt 7 s3_1519 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1519 7 _ le
  decide +kernel
theorem b3_1520 : Blocked tgt 7 s3_1520 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1520 7 _ le
  decide +kernel
theorem b3_1521 : Blocked tgt 7 s3_1521 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1521 7 _ le
  decide +kernel
theorem b3_1522 : Blocked tgt 7 s3_1522 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1522 7 _ le
  decide +kernel
theorem b3_1523 : Blocked tgt 7 s3_1523 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1523 7 _ le
  decide +kernel
theorem b3_1524 : Blocked tgt 7 s3_1524 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1524 7 _ le
  decide +kernel
theorem b3_1525 : Blocked tgt 7 s3_1525 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1525 7 _ le
  decide +kernel
theorem b3_1526 : Blocked tgt 7 s3_1526 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1527 : Blocked tgt 7 s3_1527 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1528 : Blocked tgt 7 s3_1528 := by
  apply node_sound (nxt := [s4_26])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_26
theorem b3_1529 : Blocked tgt 7 s3_1529 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1530 : Blocked tgt 7 s3_1530 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1530 7 _ le
  decide +kernel
theorem b3_1531 : Blocked tgt 7 s3_1531 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1531 7 _ le
  decide +kernel
theorem b3_1532 : Blocked tgt 7 s3_1532 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1532 7 _ le
  decide +kernel
theorem b3_1533 : Blocked tgt 7 s3_1533 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s3_1533 7 _ le
  decide +kernel
theorem b3_1534 : Blocked tgt 7 s3_1534 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1534 7 _ le
  decide +kernel
theorem b3_1535 : Blocked tgt 7 s3_1535 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s3_1535 7 _ le
  decide +kernel
end ThetaCert
