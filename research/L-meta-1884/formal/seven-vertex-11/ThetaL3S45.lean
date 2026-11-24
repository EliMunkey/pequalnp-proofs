import ThetaAlias
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1080 : Blocked tgt 7 s3_1080 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1081 : Blocked tgt 7 s3_1081 := by
  apply node_sound (nxt := [s4_26])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_26
theorem b3_1082 : Blocked tgt 7 s3_1082 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1082 7 _ le
  decide +kernel
theorem b3_1083 : Blocked tgt 7 s3_1083 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1083 7 _ le
  decide +kernel
theorem b3_1084 : Blocked tgt 7 s3_1084 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1084 7 _ le
  decide +kernel
theorem b3_1085 : Blocked tgt 7 s3_1085 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1085 7 _ le
  decide +kernel
theorem b3_1086 : Blocked tgt 7 s3_1086 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1086 7 _ le
  decide +kernel
theorem b3_1087 : Blocked tgt 7 s3_1087 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1087 7 _ le
  decide +kernel
theorem b3_1088 : Blocked tgt 7 s3_1088 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_1088 7 _ le
  decide +kernel
theorem b3_1089 : Blocked tgt 7 s3_1089 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(1,false))] s3_1089 7 _ le
  decide +kernel
theorem b3_1090 : Blocked tgt 7 s3_1090 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_1090 7 _ le
  decide +kernel
theorem b3_1091 : Blocked tgt 7 s3_1091 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1091 7 _ le
  decide +kernel
theorem b3_1092 : Blocked tgt 7 s3_1092 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1092 7 _ le
  decide +kernel
theorem b3_1093 : Blocked tgt 7 s3_1093 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1094 : Blocked tgt 7 s3_1094 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1094 7 _ le
  decide +kernel
theorem b3_1095 : Blocked tgt 7 s3_1095 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1095 7 _ le
  decide +kernel
theorem b3_1096 : Blocked tgt 7 s3_1096 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(0,true))] s3_1096 7 _ le
  decide +kernel
theorem b3_1097 : Blocked tgt 7 s3_1097 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1097 7 _ le
  decide +kernel
theorem b3_1098 : Blocked tgt 7 s3_1098 := by
  apply node_sound (nxt := [s4_52,a2387])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_52
    · exact via sym2 fix2 (by decide +kernel) b4_29
theorem b3_1099 : Blocked tgt 7 s3_1099 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1099 7 _ le
  decide +kernel
theorem b3_1100 : Blocked tgt 7 s3_1100 := by
  apply node_sound (nxt := [s4_47])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_47
theorem b3_1101 : Blocked tgt 7 s3_1101 := by
  apply node_sound (nxt := [s4_52])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_52
theorem b3_1102 : Blocked tgt 7 s3_1102 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1102 7 _ le
  decide +kernel
theorem b3_1103 : Blocked tgt 7 s3_1103 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1103 7 _ le
  decide +kernel
end ThetaCert
