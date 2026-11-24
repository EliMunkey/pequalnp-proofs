import ThetaAlias
import ThetaL4S0
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1416 : Blocked tgt 7 s3_1416 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,false),(0,true))] s3_1416 7 _ le
  decide +kernel
theorem b3_1417 : Blocked tgt 7 s3_1417 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1417 7 _ le
  decide +kernel
theorem b3_1418 : Blocked tgt 7 s3_1418 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1418 7 _ le
  decide +kernel
theorem b3_1419 : Blocked tgt 7 s3_1419 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1419 7 _ le
  decide +kernel
theorem b3_1420 : Blocked tgt 7 s3_1420 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(2,true))] s3_1420 7 _ le
  decide +kernel
theorem b3_1421 : Blocked tgt 7 s3_1421 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1421 7 _ le
  decide +kernel
theorem b3_1422 : Blocked tgt 7 s3_1422 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,true))] s3_1422 7 _ le
  decide +kernel
theorem b3_1423 : Blocked tgt 7 s3_1423 := by
  apply node_sound (nxt := [s4_39,a2400,a2401])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_39
    · exact via sym2 fix2 (by decide +kernel) b4_46
    · exact via sym3 fix3 (by decide +kernel) b4_11
theorem b3_1424 : Blocked tgt 7 s3_1424 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(4,true))] s3_1424 7 _ le
  decide +kernel
theorem b3_1425 : Blocked tgt 7 s3_1425 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(3,true),(4,true))] s3_1425 7 _ le
  decide +kernel
theorem b3_1426 : Blocked tgt 7 s3_1426 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1426 7 _ le
  decide +kernel
theorem b3_1427 : Blocked tgt 7 s3_1427 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(0,true))] s3_1427 7 _ le
  decide +kernel
theorem b3_1428 : Blocked tgt 7 s3_1428 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(0,true))] s3_1428 7 _ le
  decide +kernel
theorem b3_1429 : Blocked tgt 7 s3_1429 := by
  apply node_sound (nxt := [s4_48])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_48
theorem b3_1430 : Blocked tgt 7 s3_1430 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s3_1430 7 _ le
  decide +kernel
theorem b3_1431 : Blocked tgt 7 s3_1431 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1431 7 _ le
  decide +kernel
theorem b3_1432 : Blocked tgt 7 s3_1432 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_1432 7 _ le
  decide +kernel
theorem b3_1433 : Blocked tgt 7 s3_1433 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_1433 7 _ le
  decide +kernel
theorem b3_1434 : Blocked tgt 7 s3_1434 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,true))] s3_1434 7 _ le
  decide +kernel
theorem b3_1435 : Blocked tgt 7 s3_1435 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s3_1435 7 _ le
  decide +kernel
theorem b3_1436 : Blocked tgt 7 s3_1436 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1436 7 _ le
  decide +kernel
theorem b3_1437 : Blocked tgt 7 s3_1437 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1437 7 _ le
  decide +kernel
theorem b3_1438 : Blocked tgt 7 s3_1438 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1438 7 _ le
  decide +kernel
theorem b3_1439 : Blocked tgt 7 s3_1439 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1439 7 _ le
  decide +kernel
end ThetaCert
