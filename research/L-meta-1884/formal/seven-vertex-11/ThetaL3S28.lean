import ThetaAlias
import ThetaL4S0
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_672 : Blocked tgt 7 s3_672 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_673 : Blocked tgt 7 s3_673 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_673 7 _ le
  decide +kernel
theorem b3_674 : Blocked tgt 7 s3_674 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_674 7 _ le
  decide +kernel
theorem b3_675 : Blocked tgt 7 s3_675 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_675 7 _ le
  decide +kernel
theorem b3_676 : Blocked tgt 7 s3_676 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_676 7 _ le
  decide +kernel
theorem b3_677 : Blocked tgt 7 s3_677 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_677 7 _ le
  decide +kernel
theorem b3_678 : Blocked tgt 7 s3_678 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_678 7 _ le
  decide +kernel
theorem b3_679 : Blocked tgt 7 s3_679 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_679 7 _ le
  decide +kernel
theorem b3_680 : Blocked tgt 7 s3_680 := by
  apply node_sound (nxt := [s4_7,s4_6])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_7
    · exact b4_6
theorem b3_681 : Blocked tgt 7 s3_681 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_682 : Blocked tgt 7 s3_682 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_682 7 _ le
  decide +kernel
theorem b3_683 : Blocked tgt 7 s3_683 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_683 7 _ le
  decide +kernel
theorem b3_684 : Blocked tgt 7 s3_684 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_684 7 _ le
  decide +kernel
theorem b3_685 : Blocked tgt 7 s3_685 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_685 7 _ le
  decide +kernel
theorem b3_686 : Blocked tgt 7 s3_686 := by
  intro m le c
  apply rejects_sound extra87 i5 4 tgt small87 hot87 [] s3_686 7 _ le
  decide +kernel
theorem b3_687 : Blocked tgt 7 s3_687 := by
  apply node_sound (nxt := [s4_9,s4_4])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_9
    · exact b4_4
theorem b3_688 : Blocked tgt 7 s3_688 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_689 : Blocked tgt 7 s3_689 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_690 : Blocked tgt 7 s3_690 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_690 7 _ le
  decide +kernel
theorem b3_691 : Blocked tgt 7 s3_691 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_691 7 _ le
  decide +kernel
theorem b3_692 : Blocked tgt 7 s3_692 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_692 7 _ le
  decide +kernel
theorem b3_693 : Blocked tgt 7 s3_693 := by
  intro m le c
  apply rejects_sound extra87 i5 4 tgt small87 hot87 [] s3_693 7 _ le
  decide +kernel
theorem b3_694 : Blocked tgt 7 s3_694 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_695 : Blocked tgt 7 s3_695 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
end ThetaCert
