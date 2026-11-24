import ThetaAlias
import ThetaL4S0
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1152 : Blocked tgt 7 s3_1152 := by
  intro m le c
  apply rejects_sound extra54 i5 4 tgt small54 hot54 [] s3_1152 7 _ le
  decide +kernel
theorem b3_1153 : Blocked tgt 7 s3_1153 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1153 7 _ le
  decide +kernel
theorem b3_1154 : Blocked tgt 7 s3_1154 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1154 7 _ le
  decide +kernel
theorem b3_1155 : Blocked tgt 7 s3_1155 := by
  intro m le c
  apply rejects_sound extra54 i5 4 tgt small54 hot54 [] s3_1155 7 _ le
  decide +kernel
theorem b3_1156 : Blocked tgt 7 s3_1156 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1156 7 _ le
  decide +kernel
theorem b3_1157 : Blocked tgt 7 s3_1157 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(2,true))] s3_1157 7 _ le
  decide +kernel
theorem b3_1158 : Blocked tgt 7 s3_1158 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s3_1158 7 _ le
  decide +kernel
theorem b3_1159 : Blocked tgt 7 s3_1159 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1159 7 _ le
  decide +kernel
theorem b3_1160 : Blocked tgt 7 s3_1160 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(0,false))] s3_1160 7 _ le
  decide +kernel
theorem b3_1161 : Blocked tgt 7 s3_1161 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1161 7 _ le
  decide +kernel
theorem b3_1162 : Blocked tgt 7 s3_1162 := by
  apply node_sound (nxt := [a2394])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym1 fix1 (by decide +kernel) b4_61
theorem b3_1163 : Blocked tgt 7 s3_1163 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1163 7 _ le
  decide +kernel
theorem b3_1164 : Blocked tgt 7 s3_1164 := by
  apply node_sound (nxt := [a2395])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym2 fix2 (by decide +kernel) b4_19
theorem b3_1165 : Blocked tgt 7 s3_1165 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s3_1165 7 _ le
  decide +kernel
theorem b3_1166 : Blocked tgt 7 s3_1166 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s3_1166 7 _ le
  decide +kernel
theorem b3_1167 : Blocked tgt 7 s3_1167 := by
  intro m le c
  apply rejects_sound extra54 i5 4 tgt small54 hot54 [] s3_1167 7 _ le
  decide +kernel
theorem b3_1168 : Blocked tgt 7 s3_1168 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,false))] s3_1168 7 _ le
  decide +kernel
theorem b3_1169 : Blocked tgt 7 s3_1169 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1169 7 _ le
  decide +kernel
theorem b3_1170 : Blocked tgt 7 s3_1170 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,false))] s3_1170 7 _ le
  decide +kernel
theorem b3_1171 : Blocked tgt 7 s3_1171 := by
  apply node_sound (nxt := [a2396])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym1 fix1 (by decide +kernel) b4_60
theorem b3_1172 : Blocked tgt 7 s3_1172 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1172 7 _ le
  decide +kernel
theorem b3_1173 : Blocked tgt 7 s3_1173 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1174 : Blocked tgt 7 s3_1174 := by
  apply node_sound (nxt := [s4_34,s4_47])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_34
    · exact b4_47
theorem b3_1175 : Blocked tgt 7 s3_1175 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1175 7 _ le
  decide +kernel
end ThetaCert
