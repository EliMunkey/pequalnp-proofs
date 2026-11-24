import ThetaAlias
import ThetaL4S0
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_720 : Blocked tgt 7 s3_720 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_720 7 _ le
  decide +kernel
theorem b3_721 : Blocked tgt 7 s3_721 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_721 7 _ le
  decide +kernel
theorem b3_722 : Blocked tgt 7 s3_722 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_722 7 _ le
  decide +kernel
theorem b3_723 : Blocked tgt 7 s3_723 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_723 7 _ le
  decide +kernel
theorem b3_724 : Blocked tgt 7 s3_724 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_724 7 _ le
  decide +kernel
theorem b3_725 : Blocked tgt 7 s3_725 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_725 7 _ le
  decide +kernel
theorem b3_726 : Blocked tgt 7 s3_726 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_727 : Blocked tgt 7 s3_727 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_727 7 _ le
  decide +kernel
theorem b3_728 : Blocked tgt 7 s3_728 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_728 7 _ le
  decide +kernel
theorem b3_729 : Blocked tgt 7 s3_729 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_729 7 _ le
  decide +kernel
theorem b3_730 : Blocked tgt 7 s3_730 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(4,true))] s3_730 7 _ le
  decide +kernel
theorem b3_731 : Blocked tgt 7 s3_731 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(4,true))] s3_731 7 _ le
  decide +kernel
theorem b3_732 : Blocked tgt 7 s3_732 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_732 7 _ le
  decide +kernel
theorem b3_733 : Blocked tgt 7 s3_733 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_734 : Blocked tgt 7 s3_734 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_734 7 _ le
  decide +kernel
theorem b3_735 : Blocked tgt 7 s3_735 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(4,true))] s3_735 7 _ le
  decide +kernel
theorem b3_736 : Blocked tgt 7 s3_736 := by
  apply node_sound (nxt := [s4_13,s4_12])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_13
    · exact b4_12
theorem b3_737 : Blocked tgt 7 s3_737 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_737 7 _ le
  decide +kernel
theorem b3_738 : Blocked tgt 7 s3_738 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_738 7 _ le
  decide +kernel
theorem b3_739 : Blocked tgt 7 s3_739 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(1,false))] s3_739 7 _ le
  decide +kernel
theorem b3_740 : Blocked tgt 7 s3_740 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_740 7 _ le
  decide +kernel
theorem b3_741 : Blocked tgt 7 s3_741 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_741 7 _ le
  decide +kernel
theorem b3_742 : Blocked tgt 7 s3_742 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_742 7 _ le
  decide +kernel
theorem b3_743 : Blocked tgt 7 s3_743 := by
  intro m le c
  apply rejects_sound extra37 i5 4 tgt small37 hot37 [] s3_743 7 _ le
  decide +kernel
end ThetaCert
