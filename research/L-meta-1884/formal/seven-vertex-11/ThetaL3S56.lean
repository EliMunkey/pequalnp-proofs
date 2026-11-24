import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1344 : Blocked tgt 7 s3_1344 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,true),(3,true))] s3_1344 7 _ le
  decide +kernel
theorem b3_1345 : Blocked tgt 7 s3_1345 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1345 7 _ le
  decide +kernel
theorem b3_1346 : Blocked tgt 7 s3_1346 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1346 7 _ le
  decide +kernel
theorem b3_1347 : Blocked tgt 7 s3_1347 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1347 7 _ le
  decide +kernel
theorem b3_1348 : Blocked tgt 7 s3_1348 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1348 7 _ le
  decide +kernel
theorem b3_1349 : Blocked tgt 7 s3_1349 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1349 7 _ le
  decide +kernel
theorem b3_1350 : Blocked tgt 7 s3_1350 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,true),(3,true))] s3_1350 7 _ le
  decide +kernel
theorem b3_1351 : Blocked tgt 7 s3_1351 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1351 7 _ le
  decide +kernel
theorem b3_1352 : Blocked tgt 7 s3_1352 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_1352 7 _ le
  decide +kernel
theorem b3_1353 : Blocked tgt 7 s3_1353 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1353 7 _ le
  decide +kernel
theorem b3_1354 : Blocked tgt 7 s3_1354 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1354 7 _ le
  decide +kernel
theorem b3_1355 : Blocked tgt 7 s3_1355 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1355 7 _ le
  decide +kernel
theorem b3_1356 : Blocked tgt 7 s3_1356 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1356 7 _ le
  decide +kernel
theorem b3_1357 : Blocked tgt 7 s3_1357 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1357 7 _ le
  decide +kernel
theorem b3_1358 : Blocked tgt 7 s3_1358 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1358 7 _ le
  decide +kernel
theorem b3_1359 : Blocked tgt 7 s3_1359 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1359 7 _ le
  decide +kernel
theorem b3_1360 : Blocked tgt 7 s3_1360 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1360 7 _ le
  decide +kernel
theorem b3_1361 : Blocked tgt 7 s3_1361 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1361 7 _ le
  decide +kernel
theorem b3_1362 : Blocked tgt 7 s3_1362 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_1362 7 _ le
  decide +kernel
theorem b3_1363 : Blocked tgt 7 s3_1363 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_1363 7 _ le
  decide +kernel
theorem b3_1364 : Blocked tgt 7 s3_1364 := by
  apply node_sound (nxt := [s4_43,s4_26])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_43
    · exact b4_26
theorem b3_1365 : Blocked tgt 7 s3_1365 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_1365 7 _ le
  decide +kernel
theorem b3_1366 : Blocked tgt 7 s3_1366 := by
  apply node_sound (nxt := [s4_43])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_43
theorem b3_1367 : Blocked tgt 7 s3_1367 := by
  apply node_sound (nxt := [s4_41,s4_27])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_41
    · exact b4_27
end ThetaCert
