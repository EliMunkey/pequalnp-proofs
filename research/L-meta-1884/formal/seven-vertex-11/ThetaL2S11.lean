import ThetaAlias
import ThetaL3S3
import ThetaL3S12
import ThetaL3S53
import ThetaL3S62
import ThetaL3S63
import ThetaL3S78
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_264 : Blocked tgt 8 s2_264 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_264 8 _ le
  decide +kernel
theorem b2_265 : Blocked tgt 8 s2_265 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_265 8 _ le
  decide +kernel
theorem b2_266 : Blocked tgt 8 s2_266 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_266 8 _ le
  decide +kernel
theorem b2_267 : Blocked tgt 8 s2_267 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,false),(5,true))] s2_267 8 _ le
  decide +kernel
theorem b2_268 : Blocked tgt 8 s2_268 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_268 8 _ le
  decide +kernel
theorem b2_269 : Blocked tgt 8 s2_269 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_269 8 _ le
  decide +kernel
theorem b2_270 : Blocked tgt 8 s2_270 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_270 8 _ le
  decide +kernel
theorem b2_271 : Blocked tgt 8 s2_271 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_271 8 _ le
  decide +kernel
theorem b2_272 : Blocked tgt 8 s2_272 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_272 8 _ le
  decide +kernel
theorem b2_273 : Blocked tgt 8 s2_273 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_273 8 _ le
  decide +kernel
theorem b2_274 : Blocked tgt 8 s2_274 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_274 8 _ le
  decide +kernel
theorem b2_275 : Blocked tgt 8 s2_275 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_275 8 _ le
  decide +kernel
theorem b2_276 : Blocked tgt 8 s2_276 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_276 8 _ le
  decide +kernel
theorem b2_277 : Blocked tgt 8 s2_277 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_277 8 _ le
  decide +kernel
theorem b2_278 : Blocked tgt 8 s2_278 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_278 8 _ le
  decide +kernel
theorem b2_279 : Blocked tgt 8 s2_279 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_279 8 _ le
  decide +kernel
theorem b2_280 : Blocked tgt 8 s2_280 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_280 8 _ le
  decide +kernel
theorem b2_281 : Blocked tgt 8 s2_281 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_281 8 _ le
  decide +kernel
theorem b2_282 : Blocked tgt 8 s2_282 := by
  apply node_sound (nxt := [a933,a934,s3_311,s3_89,a935,s3_1528])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) b3_1282
    · exact via sym2 fix2 (by decide +kernel) b3_1893
    · exact b3_311
    · exact b3_89
    · exact via sym1 fix1 (by decide +kernel) b3_1511
    · exact b3_1528
theorem b2_283 : Blocked tgt 8 s2_283 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_283 8 _ le
  decide +kernel
theorem b2_284 : Blocked tgt 8 s2_284 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_284 8 _ le
  decide +kernel
theorem b2_285 : Blocked tgt 8 s2_285 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_285 8 _ le
  decide +kernel
theorem b2_286 : Blocked tgt 8 s2_286 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_286 8 _ le
  decide +kernel
theorem b2_287 : Blocked tgt 8 s2_287 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_287 8 _ le
  decide +kernel
end ThetaCert
