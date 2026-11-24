import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1200 : Blocked tgt 7 s3_1200 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s3_1200 7 _ le
  decide +kernel
theorem b3_1201 : Blocked tgt 7 s3_1201 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s3_1201 7 _ le
  decide +kernel
theorem b3_1202 : Blocked tgt 7 s3_1202 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(5,true))] s3_1202 7 _ le
  decide +kernel
theorem b3_1203 : Blocked tgt 7 s3_1203 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(2,true))] s3_1203 7 _ le
  decide +kernel
theorem b3_1204 : Blocked tgt 7 s3_1204 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(5,true))] s3_1204 7 _ le
  decide +kernel
theorem b3_1205 : Blocked tgt 7 s3_1205 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1205 7 _ le
  decide +kernel
theorem b3_1206 : Blocked tgt 7 s3_1206 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1206 7 _ le
  decide +kernel
theorem b3_1207 : Blocked tgt 7 s3_1207 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1207 7 _ le
  decide +kernel
theorem b3_1208 : Blocked tgt 7 s3_1208 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1208 7 _ le
  decide +kernel
theorem b3_1209 : Blocked tgt 7 s3_1209 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1209 7 _ le
  decide +kernel
theorem b3_1210 : Blocked tgt 7 s3_1210 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1210 7 _ le
  decide +kernel
theorem b3_1211 : Blocked tgt 7 s3_1211 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1211 7 _ le
  decide +kernel
theorem b3_1212 : Blocked tgt 7 s3_1212 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1212 7 _ le
  decide +kernel
theorem b3_1213 : Blocked tgt 7 s3_1213 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_1213 7 _ le
  decide +kernel
theorem b3_1214 : Blocked tgt 7 s3_1214 := by
  apply node_sound (nxt := [s4_26])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_26
theorem b3_1215 : Blocked tgt 7 s3_1215 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1215 7 _ le
  decide +kernel
theorem b3_1216 : Blocked tgt 7 s3_1216 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1216 7 _ le
  decide +kernel
theorem b3_1217 : Blocked tgt 7 s3_1217 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1217 7 _ le
  decide +kernel
theorem b3_1218 : Blocked tgt 7 s3_1218 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1218 7 _ le
  decide +kernel
theorem b3_1219 : Blocked tgt 7 s3_1219 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1219 7 _ le
  decide +kernel
theorem b3_1220 : Blocked tgt 7 s3_1220 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1220 7 _ le
  decide +kernel
theorem b3_1221 : Blocked tgt 7 s3_1221 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1221 7 _ le
  decide +kernel
theorem b3_1222 : Blocked tgt 7 s3_1222 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_1222 7 _ le
  decide +kernel
theorem b3_1223 : Blocked tgt 7 s3_1223 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1223 7 _ le
  decide +kernel
end ThetaCert
