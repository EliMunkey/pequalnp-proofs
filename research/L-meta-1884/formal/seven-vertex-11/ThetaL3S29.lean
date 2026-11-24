import ThetaAlias
import ThetaL4S0
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_696 : Blocked tgt 7 s3_696 := by
  apply node_sound (nxt := [s4_8,s4_5])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_8
    · exact b4_5
theorem b3_697 : Blocked tgt 7 s3_697 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_697 7 _ le
  decide +kernel
theorem b3_698 : Blocked tgt 7 s3_698 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_698 7 _ le
  decide +kernel
theorem b3_699 : Blocked tgt 7 s3_699 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_699 7 _ le
  decide +kernel
theorem b3_700 : Blocked tgt 7 s3_700 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_700 7 _ le
  decide +kernel
theorem b3_701 : Blocked tgt 7 s3_701 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_701 7 _ le
  decide +kernel
theorem b3_702 : Blocked tgt 7 s3_702 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_702 7 _ le
  decide +kernel
theorem b3_703 : Blocked tgt 7 s3_703 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_703 7 _ le
  decide +kernel
theorem b3_704 : Blocked tgt 7 s3_704 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_704 7 _ le
  decide +kernel
theorem b3_705 : Blocked tgt 7 s3_705 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_705 7 _ le
  decide +kernel
theorem b3_706 : Blocked tgt 7 s3_706 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_706 7 _ le
  decide +kernel
theorem b3_707 : Blocked tgt 7 s3_707 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_707 7 _ le
  decide +kernel
theorem b3_708 : Blocked tgt 7 s3_708 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_708 7 _ le
  decide +kernel
theorem b3_709 : Blocked tgt 7 s3_709 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_709 7 _ le
  decide +kernel
theorem b3_710 : Blocked tgt 7 s3_710 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_710 7 _ le
  decide +kernel
theorem b3_711 : Blocked tgt 7 s3_711 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_711 7 _ le
  decide +kernel
theorem b3_712 : Blocked tgt 7 s3_712 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_712 7 _ le
  decide +kernel
theorem b3_713 : Blocked tgt 7 s3_713 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_713 7 _ le
  decide +kernel
theorem b3_714 : Blocked tgt 7 s3_714 := by
  apply node_sound (nxt := [s4_11,s4_10])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_11
    · exact b4_10
theorem b3_715 : Blocked tgt 7 s3_715 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_716 : Blocked tgt 7 s3_716 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_716 7 _ le
  decide +kernel
theorem b3_717 : Blocked tgt 7 s3_717 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_717 7 _ le
  decide +kernel
theorem b3_718 : Blocked tgt 7 s3_718 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_719 : Blocked tgt 7 s3_719 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
end ThetaCert
