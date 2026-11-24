import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b4_0 : Blocked tgt 6 s4_0 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true))] s4_0 6 _ le
  decide +kernel
theorem b4_1 : Blocked tgt 6 s4_1 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s4_1 6 _ le
  decide +kernel
theorem b4_2 : Blocked tgt 6 s4_2 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s4_2 6 _ le
  decide +kernel
theorem b4_3 : Blocked tgt 6 s4_3 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_4 : Blocked tgt 6 s4_4 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_5 : Blocked tgt 6 s4_5 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_6 : Blocked tgt 6 s4_6 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_7 : Blocked tgt 6 s4_7 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(4,true)),(false,(0,true),(6,true))] s4_7 6 _ le
  decide +kernel
theorem b4_8 : Blocked tgt 6 s4_8 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s4_8 6 _ le
  decide +kernel
theorem b4_9 : Blocked tgt 6 s4_9 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s4_9 6 _ le
  decide +kernel
theorem b4_10 : Blocked tgt 6 s4_10 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_11 : Blocked tgt 6 s4_11 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_12 : Blocked tgt 6 s4_12 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_13 : Blocked tgt 6 s4_13 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_13 6 _ le
  decide +kernel
theorem b4_14 : Blocked tgt 6 s4_14 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true)),(false,(3,true),(0,true))] s4_14 6 _ le
  decide +kernel
theorem b4_15 : Blocked tgt 6 s4_15 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(3,true)),(false,(0,true),(5,true))] s4_15 6 _ le
  decide +kernel
theorem b4_16 : Blocked tgt 6 s4_16 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(5,true)),(false,(2,true),(0,true))] s4_16 6 _ le
  decide +kernel
theorem b4_17 : Blocked tgt 6 s4_17 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(1,false))] s4_17 6 _ le
  decide +kernel
theorem b4_18 : Blocked tgt 6 s4_18 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s4_18 6 _ le
  decide +kernel
theorem b4_19 : Blocked tgt 6 s4_19 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s4_19 6 _ le
  decide +kernel
theorem b4_20 : Blocked tgt 6 s4_20 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_20 6 _ le
  decide +kernel
theorem b4_21 : Blocked tgt 6 s4_21 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s4_21 6 _ le
  decide +kernel
theorem b4_22 : Blocked tgt 6 s4_22 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s4_22 6 _ le
  decide +kernel
theorem b4_23 : Blocked tgt 6 s4_23 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_23 6 _ le
  decide +kernel
end ThetaCert
