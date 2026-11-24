import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1392 : Blocked tgt 7 s3_1392 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1392 7 _ le
  decide +kernel
theorem b3_1393 : Blocked tgt 7 s3_1393 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1393 7 _ le
  decide +kernel
theorem b3_1394 : Blocked tgt 7 s3_1394 := by
  intro m le c
  apply rejects_sound extra44 i5 4 tgt small44 hot44 [] s3_1394 7 _ le
  decide +kernel
theorem b3_1395 : Blocked tgt 7 s3_1395 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1395 7 _ le
  decide +kernel
theorem b3_1396 : Blocked tgt 7 s3_1396 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1396 7 _ le
  decide +kernel
theorem b3_1397 : Blocked tgt 7 s3_1397 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s3_1397 7 _ le
  decide +kernel
theorem b3_1398 : Blocked tgt 7 s3_1398 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1398 7 _ le
  decide +kernel
theorem b3_1399 : Blocked tgt 7 s3_1399 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s3_1399 7 _ le
  decide +kernel
theorem b3_1400 : Blocked tgt 7 s3_1400 := by
  apply node_sound (nxt := [s4_45,a2398])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_45
    · exact via sym1 fix1 (by decide +kernel) b4_45
theorem b3_1401 : Blocked tgt 7 s3_1401 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1401 7 _ le
  decide +kernel
theorem b3_1402 : Blocked tgt 7 s3_1402 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1402 7 _ le
  decide +kernel
theorem b3_1403 : Blocked tgt 7 s3_1403 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1403 7 _ le
  decide +kernel
theorem b3_1404 : Blocked tgt 7 s3_1404 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1404 7 _ le
  decide +kernel
theorem b3_1405 : Blocked tgt 7 s3_1405 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1406 : Blocked tgt 7 s3_1406 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1406 7 _ le
  decide +kernel
theorem b3_1407 : Blocked tgt 7 s3_1407 := by
  apply node_sound (nxt := [s4_37])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_37
theorem b3_1408 : Blocked tgt 7 s3_1408 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1408 7 _ le
  decide +kernel
theorem b3_1409 : Blocked tgt 7 s3_1409 := by
  apply node_sound (nxt := [a2399])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym2 fix2 (by decide +kernel) b4_37
theorem b3_1410 : Blocked tgt 7 s3_1410 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1411 : Blocked tgt 7 s3_1411 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1412 : Blocked tgt 7 s3_1412 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1413 : Blocked tgt 7 s3_1413 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1413 7 _ le
  decide +kernel
theorem b3_1414 : Blocked tgt 7 s3_1414 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1414 7 _ le
  decide +kernel
theorem b3_1415 : Blocked tgt 7 s3_1415 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1415 7 _ le
  decide +kernel
end ThetaCert
