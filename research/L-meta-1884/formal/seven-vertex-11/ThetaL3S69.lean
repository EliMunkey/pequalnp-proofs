import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1656 : Blocked tgt 7 s3_1656 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1656 7 _ le
  decide +kernel
theorem b3_1657 : Blocked tgt 7 s3_1657 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1657 7 _ le
  decide +kernel
theorem b3_1658 : Blocked tgt 7 s3_1658 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1658 7 _ le
  decide +kernel
theorem b3_1659 : Blocked tgt 7 s3_1659 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1659 7 _ le
  decide +kernel
theorem b3_1660 : Blocked tgt 7 s3_1660 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1660 7 _ le
  decide +kernel
theorem b3_1661 : Blocked tgt 7 s3_1661 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1661 7 _ le
  decide +kernel
theorem b3_1662 : Blocked tgt 7 s3_1662 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s3_1662 7 _ le
  decide +kernel
theorem b3_1663 : Blocked tgt 7 s3_1663 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_1663 7 _ le
  decide +kernel
theorem b3_1664 : Blocked tgt 7 s3_1664 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1664 7 _ le
  decide +kernel
theorem b3_1665 : Blocked tgt 7 s3_1665 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_1665 7 _ le
  decide +kernel
theorem b3_1666 : Blocked tgt 7 s3_1666 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1666 7 _ le
  decide +kernel
theorem b3_1667 : Blocked tgt 7 s3_1667 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_1667 7 _ le
  decide +kernel
theorem b3_1668 : Blocked tgt 7 s3_1668 := by
  apply node_sound (nxt := [a2402])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym3 fix3 (by decide +kernel) b4_50
theorem b3_1669 : Blocked tgt 7 s3_1669 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1669 7 _ le
  decide +kernel
theorem b3_1670 : Blocked tgt 7 s3_1670 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1670 7 _ le
  decide +kernel
theorem b3_1671 : Blocked tgt 7 s3_1671 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1671 7 _ le
  decide +kernel
theorem b3_1672 : Blocked tgt 7 s3_1672 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s3_1672 7 _ le
  decide +kernel
theorem b3_1673 : Blocked tgt 7 s3_1673 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s3_1673 7 _ le
  decide +kernel
theorem b3_1674 : Blocked tgt 7 s3_1674 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s3_1674 7 _ le
  decide +kernel
theorem b3_1675 : Blocked tgt 7 s3_1675 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_1675 7 _ le
  decide +kernel
theorem b3_1676 : Blocked tgt 7 s3_1676 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1676 7 _ le
  decide +kernel
theorem b3_1677 : Blocked tgt 7 s3_1677 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_1677 7 _ le
  decide +kernel
theorem b3_1678 : Blocked tgt 7 s3_1678 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1678 7 _ le
  decide +kernel
theorem b3_1679 : Blocked tgt 7 s3_1679 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_1679 7 _ le
  decide +kernel
end ThetaCert
