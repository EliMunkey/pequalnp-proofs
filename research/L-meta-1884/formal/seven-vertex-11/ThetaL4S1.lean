import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b4_24 : Blocked tgt 6 s4_24 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s4_24 6 _ le
  decide +kernel
theorem b4_25 : Blocked tgt 6 s4_25 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s4_25 6 _ le
  decide +kernel
theorem b4_26 : Blocked tgt 6 s4_26 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s4_26 6 _ le
  decide +kernel
theorem b4_27 : Blocked tgt 6 s4_27 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_28 : Blocked tgt 6 s4_28 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_29 : Blocked tgt 6 s4_29 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s4_29 6 _ le
  decide +kernel
theorem b4_30 : Blocked tgt 6 s4_30 := by
  intro m le c
  apply rejects_sound extra16 i5 4 tgt small16 hot16 [] s4_30 6 _ le
  decide +kernel
theorem b4_31 : Blocked tgt 6 s4_31 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_31 6 _ le
  decide +kernel
theorem b4_32 : Blocked tgt 6 s4_32 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_32 6 _ le
  decide +kernel
theorem b4_33 : Blocked tgt 6 s4_33 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_33 6 _ le
  decide +kernel
theorem b4_34 : Blocked tgt 6 s4_34 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_34 6 _ le
  decide +kernel
theorem b4_35 : Blocked tgt 6 s4_35 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s4_35 6 _ le
  decide +kernel
theorem b4_36 : Blocked tgt 6 s4_36 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_36 6 _ le
  decide +kernel
theorem b4_37 : Blocked tgt 6 s4_37 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s4_37 6 _ le
  decide +kernel
theorem b4_38 : Blocked tgt 6 s4_38 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,false))] s4_38 6 _ le
  decide +kernel
theorem b4_39 : Blocked tgt 6 s4_39 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_40 : Blocked tgt 6 s4_40 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_40 6 _ le
  decide +kernel
theorem b4_41 : Blocked tgt 6 s4_41 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_41 6 _ le
  decide +kernel
theorem b4_42 : Blocked tgt 6 s4_42 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_42 6 _ le
  decide +kernel
theorem b4_43 : Blocked tgt 6 s4_43 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_43 6 _ le
  decide +kernel
theorem b4_44 : Blocked tgt 6 s4_44 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(2,true))] s4_44 6 _ le
  decide +kernel
theorem b4_45 : Blocked tgt 6 s4_45 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_45 6 _ le
  decide +kernel
theorem b4_46 : Blocked tgt 6 s4_46 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,false),(0,true))] s4_46 6 _ le
  decide +kernel
theorem b4_47 : Blocked tgt 6 s4_47 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s4_47 6 _ le
  decide +kernel
end ThetaCert
