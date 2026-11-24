import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1176 : Blocked tgt 7 s3_1176 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1177 : Blocked tgt 7 s3_1177 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(4,true))] s3_1177 7 _ le
  decide +kernel
theorem b3_1178 : Blocked tgt 7 s3_1178 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1179 : Blocked tgt 7 s3_1179 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,false))] s3_1179 7 _ le
  decide +kernel
theorem b3_1180 : Blocked tgt 7 s3_1180 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1180 7 _ le
  decide +kernel
theorem b3_1181 : Blocked tgt 7 s3_1181 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1182 : Blocked tgt 7 s3_1182 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,false))] s3_1182 7 _ le
  decide +kernel
theorem b3_1183 : Blocked tgt 7 s3_1183 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(3,true),(4,true))] s3_1183 7 _ le
  decide +kernel
theorem b3_1184 : Blocked tgt 7 s3_1184 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1185 : Blocked tgt 7 s3_1185 := by
  apply node_sound (nxt := [a2397])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym1 fix1 (by decide +kernel) b4_38
theorem b3_1186 : Blocked tgt 7 s3_1186 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,false))] s3_1186 7 _ le
  decide +kernel
theorem b3_1187 : Blocked tgt 7 s3_1187 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1187 7 _ le
  decide +kernel
theorem b3_1188 : Blocked tgt 7 s3_1188 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1189 : Blocked tgt 7 s3_1189 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1190 : Blocked tgt 7 s3_1190 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1190 7 _ le
  decide +kernel
theorem b3_1191 : Blocked tgt 7 s3_1191 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,false),(5,true))] s3_1191 7 _ le
  decide +kernel
theorem b3_1192 : Blocked tgt 7 s3_1192 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1192 7 _ le
  decide +kernel
theorem b3_1193 : Blocked tgt 7 s3_1193 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1193 7 _ le
  decide +kernel
theorem b3_1194 : Blocked tgt 7 s3_1194 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,true),(3,true))] s3_1194 7 _ le
  decide +kernel
theorem b3_1195 : Blocked tgt 7 s3_1195 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1195 7 _ le
  decide +kernel
theorem b3_1196 : Blocked tgt 7 s3_1196 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1196 7 _ le
  decide +kernel
theorem b3_1197 : Blocked tgt 7 s3_1197 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1197 7 _ le
  decide +kernel
theorem b3_1198 : Blocked tgt 7 s3_1198 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1198 7 _ le
  decide +kernel
theorem b3_1199 : Blocked tgt 7 s3_1199 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s3_1199 7 _ le
  decide +kernel
end ThetaCert
