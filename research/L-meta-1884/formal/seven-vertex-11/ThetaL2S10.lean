import ThetaAlias
import ThetaL3S3
import ThetaL3S4
import ThetaL3S9
import ThetaL3S12
import ThetaL3S14
import ThetaL3S15
import ThetaL3S42
import ThetaL3S43
import ThetaL3S44
import ThetaL3S45
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_240 : Blocked tgt 8 s2_240 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_240 8 _ le
  decide +kernel
theorem b2_241 : Blocked tgt 8 s2_241 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_241 8 _ le
  decide +kernel
theorem b2_242 : Blocked tgt 8 s2_242 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_242 8 _ le
  decide +kernel
theorem b2_243 : Blocked tgt 8 s2_243 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_243 8 _ le
  decide +kernel
theorem b2_244 : Blocked tgt 8 s2_244 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_244 8 _ le
  decide +kernel
theorem b2_245 : Blocked tgt 8 s2_245 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_245 8 _ le
  decide +kernel
theorem b2_246 : Blocked tgt 8 s2_246 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_246 8 _ le
  decide +kernel
theorem b2_247 : Blocked tgt 8 s2_247 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_247 8 _ le
  decide +kernel
theorem b2_248 : Blocked tgt 8 s2_248 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_248 8 _ le
  decide +kernel
theorem b2_249 : Blocked tgt 8 s2_249 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_249 8 _ le
  decide +kernel
theorem b2_250 : Blocked tgt 8 s2_250 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_250 8 _ le
  decide +kernel
theorem b2_251 : Blocked tgt 8 s2_251 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_251 8 _ le
  decide +kernel
theorem b2_252 : Blocked tgt 8 s2_252 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_252 8 _ le
  decide +kernel
theorem b2_253 : Blocked tgt 8 s2_253 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_253 8 _ le
  decide +kernel
theorem b2_254 : Blocked tgt 8 s2_254 := by
  apply node_sound (nxt := [s3_93,s3_306,a931,s3_1081,a932,s3_1065,s3_233,s3_100,s3_355,s3_368])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_93
    · exact b3_306
    · exact via sym1 fix1 (by decide +kernel) b3_1024
    · exact b3_1081
    · exact via sym1 fix1 (by decide +kernel) b3_1043
    · exact b3_1065
    · exact b3_233
    · exact b3_100
    · exact b3_355
    · exact b3_368
theorem b2_255 : Blocked tgt 8 s2_255 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_255 8 _ le
  decide +kernel
theorem b2_256 : Blocked tgt 8 s2_256 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_256 8 _ le
  decide +kernel
theorem b2_257 : Blocked tgt 8 s2_257 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_257 8 _ le
  decide +kernel
theorem b2_258 : Blocked tgt 8 s2_258 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_258 8 _ le
  decide +kernel
theorem b2_259 : Blocked tgt 8 s2_259 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_259 8 _ le
  decide +kernel
theorem b2_260 : Blocked tgt 8 s2_260 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,false),(5,true))] s2_260 8 _ le
  decide +kernel
theorem b2_261 : Blocked tgt 8 s2_261 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_261 8 _ le
  decide +kernel
theorem b2_262 : Blocked tgt 8 s2_262 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_262 8 _ le
  decide +kernel
theorem b2_263 : Blocked tgt 8 s2_263 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_263 8 _ le
  decide +kernel
end ThetaCert
