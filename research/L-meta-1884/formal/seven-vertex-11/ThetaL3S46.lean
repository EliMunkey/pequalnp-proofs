import ThetaAlias
import ThetaL4S0
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1104 : Blocked tgt 7 s3_1104 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1104 7 _ le
  decide +kernel
theorem b3_1105 : Blocked tgt 7 s3_1105 := by
  apply node_sound (nxt := [a2388,a2389])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_31
    · exact via sym3 fix3 (by decide +kernel) b4_3
theorem b3_1106 : Blocked tgt 7 s3_1106 := by
  apply node_sound (nxt := [a2390,a2391])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_32
    · exact via sym3 fix3 (by decide +kernel) b4_6
theorem b3_1107 : Blocked tgt 7 s3_1107 := by
  apply node_sound (nxt := [s4_63])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_63
theorem b3_1108 : Blocked tgt 7 s3_1108 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1109 : Blocked tgt 7 s3_1109 := by
  apply node_sound (nxt := [s4_62,a2392,a2393])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_62
    · exact via sym2 fix2 (by decide +kernel) b4_33
    · exact via sym3 fix3 (by decide +kernel) b4_10
theorem b3_1110 : Blocked tgt 7 s3_1110 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1110 7 _ le
  decide +kernel
theorem b3_1111 : Blocked tgt 7 s3_1111 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1112 : Blocked tgt 7 s3_1112 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1113 : Blocked tgt 7 s3_1113 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1114 : Blocked tgt 7 s3_1114 := by
  apply node_sound (nxt := [s4_35])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_35
theorem b3_1115 : Blocked tgt 7 s3_1115 := by
  apply node_sound (nxt := [s4_36])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_36
theorem b3_1116 : Blocked tgt 7 s3_1116 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1116 7 _ le
  decide +kernel
theorem b3_1117 : Blocked tgt 7 s3_1117 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1117 7 _ le
  decide +kernel
theorem b3_1118 : Blocked tgt 7 s3_1118 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1118 7 _ le
  decide +kernel
theorem b3_1119 : Blocked tgt 7 s3_1119 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1119 7 _ le
  decide +kernel
theorem b3_1120 : Blocked tgt 7 s3_1120 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1120 7 _ le
  decide +kernel
theorem b3_1121 : Blocked tgt 7 s3_1121 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1121 7 _ le
  decide +kernel
theorem b3_1122 : Blocked tgt 7 s3_1122 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1122 7 _ le
  decide +kernel
theorem b3_1123 : Blocked tgt 7 s3_1123 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1123 7 _ le
  decide +kernel
theorem b3_1124 : Blocked tgt 7 s3_1124 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1124 7 _ le
  decide +kernel
theorem b3_1125 : Blocked tgt 7 s3_1125 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1125 7 _ le
  decide +kernel
theorem b3_1126 : Blocked tgt 7 s3_1126 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1126 7 _ le
  decide +kernel
theorem b3_1127 : Blocked tgt 7 s3_1127 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1127 7 _ le
  decide +kernel
end ThetaCert
