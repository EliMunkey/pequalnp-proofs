import ThetaAlias
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1368 : Blocked tgt 7 s3_1368 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(4,true))] s3_1368 7 _ le
  decide +kernel
theorem b3_1369 : Blocked tgt 7 s3_1369 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s3_1369 7 _ le
  decide +kernel
theorem b3_1370 : Blocked tgt 7 s3_1370 := by
  apply node_sound (nxt := [s4_42,s4_28])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_42
    · exact b4_28
theorem b3_1371 : Blocked tgt 7 s3_1371 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1371 7 _ le
  decide +kernel
theorem b3_1372 : Blocked tgt 7 s3_1372 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_1372 7 _ le
  decide +kernel
theorem b3_1373 : Blocked tgt 7 s3_1373 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1373 7 _ le
  decide +kernel
theorem b3_1374 : Blocked tgt 7 s3_1374 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_1374 7 _ le
  decide +kernel
theorem b3_1375 : Blocked tgt 7 s3_1375 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1375 7 _ le
  decide +kernel
theorem b3_1376 : Blocked tgt 7 s3_1376 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1376 7 _ le
  decide +kernel
theorem b3_1377 : Blocked tgt 7 s3_1377 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(4,true))] s3_1377 7 _ le
  decide +kernel
theorem b3_1378 : Blocked tgt 7 s3_1378 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1378 7 _ le
  decide +kernel
theorem b3_1379 : Blocked tgt 7 s3_1379 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1379 7 _ le
  decide +kernel
theorem b3_1380 : Blocked tgt 7 s3_1380 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1380 7 _ le
  decide +kernel
theorem b3_1381 : Blocked tgt 7 s3_1381 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1381 7 _ le
  decide +kernel
theorem b3_1382 : Blocked tgt 7 s3_1382 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1382 7 _ le
  decide +kernel
theorem b3_1383 : Blocked tgt 7 s3_1383 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1383 7 _ le
  decide +kernel
theorem b3_1384 : Blocked tgt 7 s3_1384 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1384 7 _ le
  decide +kernel
theorem b3_1385 : Blocked tgt 7 s3_1385 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1385 7 _ le
  decide +kernel
theorem b3_1386 : Blocked tgt 7 s3_1386 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(0,true))] s3_1386 7 _ le
  decide +kernel
theorem b3_1387 : Blocked tgt 7 s3_1387 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1387 7 _ le
  decide +kernel
theorem b3_1388 : Blocked tgt 7 s3_1388 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1388 7 _ le
  decide +kernel
theorem b3_1389 : Blocked tgt 7 s3_1389 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s3_1389 7 _ le
  decide +kernel
theorem b3_1390 : Blocked tgt 7 s3_1390 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1390 7 _ le
  decide +kernel
theorem b3_1391 : Blocked tgt 7 s3_1391 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1391 7 _ le
  decide +kernel
end ThetaCert
