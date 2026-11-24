import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1536 : Blocked tgt 7 s3_1536 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1536 7 _ le
  decide +kernel
theorem b3_1537 : Blocked tgt 7 s3_1537 := by
  intro m le c
  apply rejects_sound extra70 i5 4 tgt small70 hot70 [] s3_1537 7 _ le
  decide +kernel
theorem b3_1538 : Blocked tgt 7 s3_1538 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s3_1538 7 _ le
  decide +kernel
theorem b3_1539 : Blocked tgt 7 s3_1539 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1539 7 _ le
  decide +kernel
theorem b3_1540 : Blocked tgt 7 s3_1540 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1540 7 _ le
  decide +kernel
theorem b3_1541 : Blocked tgt 7 s3_1541 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_1541 7 _ le
  decide +kernel
theorem b3_1542 : Blocked tgt 7 s3_1542 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1542 7 _ le
  decide +kernel
theorem b3_1543 : Blocked tgt 7 s3_1543 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1543 7 _ le
  decide +kernel
theorem b3_1544 : Blocked tgt 7 s3_1544 := by
  apply node_sound (nxt := [s4_34])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_34
theorem b3_1545 : Blocked tgt 7 s3_1545 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_1545 7 _ le
  decide +kernel
theorem b3_1546 : Blocked tgt 7 s3_1546 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,true))] s3_1546 7 _ le
  decide +kernel
theorem b3_1547 : Blocked tgt 7 s3_1547 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s3_1547 7 _ le
  decide +kernel
theorem b3_1548 : Blocked tgt 7 s3_1548 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1548 7 _ le
  decide +kernel
theorem b3_1549 : Blocked tgt 7 s3_1549 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s3_1549 7 _ le
  decide +kernel
theorem b3_1550 : Blocked tgt 7 s3_1550 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s3_1550 7 _ le
  decide +kernel
theorem b3_1551 : Blocked tgt 7 s3_1551 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1551 7 _ le
  decide +kernel
theorem b3_1552 : Blocked tgt 7 s3_1552 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1552 7 _ le
  decide +kernel
theorem b3_1553 : Blocked tgt 7 s3_1553 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1553 7 _ le
  decide +kernel
theorem b3_1554 : Blocked tgt 7 s3_1554 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1554 7 _ le
  decide +kernel
theorem b3_1555 : Blocked tgt 7 s3_1555 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1555 7 _ le
  decide +kernel
theorem b3_1556 : Blocked tgt 7 s3_1556 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1556 7 _ le
  decide +kernel
theorem b3_1557 : Blocked tgt 7 s3_1557 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s3_1557 7 _ le
  decide +kernel
theorem b3_1558 : Blocked tgt 7 s3_1558 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1558 7 _ le
  decide +kernel
theorem b3_1559 : Blocked tgt 7 s3_1559 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1559 7 _ le
  decide +kernel
end ThetaCert
