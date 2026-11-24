import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_216 : Blocked tgt 7 s3_216 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_216 7 _ le
  decide +kernel
theorem b3_217 : Blocked tgt 7 s3_217 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_217 7 _ le
  decide +kernel
theorem b3_218 : Blocked tgt 7 s3_218 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_218 7 _ le
  decide +kernel
theorem b3_219 : Blocked tgt 7 s3_219 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s3_219 7 _ le
  decide +kernel
theorem b3_220 : Blocked tgt 7 s3_220 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_220 7 _ le
  decide +kernel
theorem b3_221 : Blocked tgt 7 s3_221 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_221 7 _ le
  decide +kernel
theorem b3_222 : Blocked tgt 7 s3_222 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_222 7 _ le
  decide +kernel
theorem b3_223 : Blocked tgt 7 s3_223 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_224 : Blocked tgt 7 s3_224 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_224 7 _ le
  decide +kernel
theorem b3_225 : Blocked tgt 7 s3_225 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_225 7 _ le
  decide +kernel
theorem b3_226 : Blocked tgt 7 s3_226 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_226 7 _ le
  decide +kernel
theorem b3_227 : Blocked tgt 7 s3_227 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_227 7 _ le
  decide +kernel
theorem b3_228 : Blocked tgt 7 s3_228 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_228 7 _ le
  decide +kernel
theorem b3_229 : Blocked tgt 7 s3_229 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_229 7 _ le
  decide +kernel
theorem b3_230 : Blocked tgt 7 s3_230 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_230 7 _ le
  decide +kernel
theorem b3_231 : Blocked tgt 7 s3_231 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_231 7 _ le
  decide +kernel
theorem b3_232 : Blocked tgt 7 s3_232 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_232 7 _ le
  decide +kernel
theorem b3_233 : Blocked tgt 7 s3_233 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s3_233 7 _ le
  decide +kernel
theorem b3_234 : Blocked tgt 7 s3_234 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_234 7 _ le
  decide +kernel
theorem b3_235 : Blocked tgt 7 s3_235 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(0,true))] s3_235 7 _ le
  decide +kernel
theorem b3_236 : Blocked tgt 7 s3_236 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_236 7 _ le
  decide +kernel
theorem b3_237 : Blocked tgt 7 s3_237 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,false),(1,true)),(false,(0,true),(6,true))] s3_237 7 _ le
  decide +kernel
theorem b3_238 : Blocked tgt 7 s3_238 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_238 7 _ le
  decide +kernel
theorem b3_239 : Blocked tgt 7 s3_239 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_239 7 _ le
  decide +kernel
end ThetaCert
