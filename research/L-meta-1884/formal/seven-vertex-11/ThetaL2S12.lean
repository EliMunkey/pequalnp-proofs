import ThetaAlias
import ThetaL3S0
import ThetaL3S4
import ThetaL3S9
import ThetaL3S13
import ThetaL3S67
import ThetaL3S70
import ThetaL3S73
import ThetaL3S75
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_288 : Blocked tgt 8 s2_288 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_288 8 _ le
  decide +kernel
theorem b2_289 : Blocked tgt 8 s2_289 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_289 8 _ le
  decide +kernel
theorem b2_290 : Blocked tgt 8 s2_290 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_290 8 _ le
  decide +kernel
theorem b2_291 : Blocked tgt 8 s2_291 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_291 8 _ le
  decide +kernel
theorem b2_292 : Blocked tgt 8 s2_292 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_292 8 _ le
  decide +kernel
theorem b2_293 : Blocked tgt 8 s2_293 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_293 8 _ le
  decide +kernel
theorem b2_294 : Blocked tgt 8 s2_294 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_294 8 _ le
  decide +kernel
theorem b2_295 : Blocked tgt 8 s2_295 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s2_295 8 _ le
  decide +kernel
theorem b2_296 : Blocked tgt 8 s2_296 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s2_296 8 _ le
  decide +kernel
theorem b2_297 : Blocked tgt 8 s2_297 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_297 8 _ le
  decide +kernel
theorem b2_298 : Blocked tgt 8 s2_298 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_298 8 _ le
  decide +kernel
theorem b2_299 : Blocked tgt 8 s2_299 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_299 8 _ le
  decide +kernel
theorem b2_300 : Blocked tgt 8 s2_300 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_300 8 _ le
  decide +kernel
theorem b2_301 : Blocked tgt 8 s2_301 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_301 8 _ le
  decide +kernel
theorem b2_302 : Blocked tgt 8 s2_302 := by
  apply node_sound (nxt := [s3_334,a936,a937,a938])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_334
    · exact via sym3 fix3 (by decide +kernel) b3_13
    · exact via sym1 fix1 (by decide +kernel) b3_1701
    · exact via sym2 fix2 (by decide +kernel) b3_1775
theorem b2_303 : Blocked tgt 8 s2_303 := by
  apply node_sound (nxt := [s3_235,s3_107,a939,a940,s3_335,a941,a942,a943])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_235
    · exact b3_107
    · exact via sym2 fix2 (by decide +kernel) b3_1615
    · exact via sym3 fix3 (by decide +kernel) b3_1817
    · exact b3_335
    · exact via sym3 fix3 (by decide +kernel) b3_17
    · exact via sym1 fix1 (by decide +kernel) b3_1702
    · exact via sym2 fix2 (by decide +kernel) b3_1760
theorem b2_304 : Blocked tgt 8 s2_304 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_304 8 _ le
  decide +kernel
theorem b2_305 : Blocked tgt 8 s2_305 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(3,true))] s2_305 8 _ le
  decide +kernel
theorem b2_306 : Blocked tgt 8 s2_306 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_306 8 _ le
  decide +kernel
theorem b2_307 : Blocked tgt 8 s2_307 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_307 8 _ le
  decide +kernel
theorem b2_308 : Blocked tgt 8 s2_308 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_308 8 _ le
  decide +kernel
theorem b2_309 : Blocked tgt 8 s2_309 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_309 8 _ le
  decide +kernel
theorem b2_310 : Blocked tgt 8 s2_310 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_310 8 _ le
  decide +kernel
theorem b2_311 : Blocked tgt 8 s2_311 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_311 8 _ le
  decide +kernel
end ThetaCert
