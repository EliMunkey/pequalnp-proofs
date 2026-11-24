import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b4_48 : Blocked tgt 6 s4_48 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true)),(false,(2,false),(0,true))] s4_48 6 _ le
  decide +kernel
theorem b4_49 : Blocked tgt 6 s4_49 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s4_49 6 _ le
  decide +kernel
theorem b4_50 : Blocked tgt 6 s4_50 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(4,true))] s4_50 6 _ le
  decide +kernel
theorem b4_51 : Blocked tgt 6 s4_51 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true))] s4_51 6 _ le
  decide +kernel
theorem b4_52 : Blocked tgt 6 s4_52 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_52 6 _ le
  decide +kernel
theorem b4_53 : Blocked tgt 6 s4_53 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s4_53 6 _ le
  decide +kernel
theorem b4_54 : Blocked tgt 6 s4_54 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_54 6 _ le
  decide +kernel
theorem b4_55 : Blocked tgt 6 s4_55 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s4_55 6 _ le
  decide +kernel
theorem b4_56 : Blocked tgt 6 s4_56 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_56 6 _ le
  decide +kernel
theorem b4_57 : Blocked tgt 6 s4_57 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s4_57 6 _ le
  decide +kernel
theorem b4_58 : Blocked tgt 6 s4_58 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s4_58 6 _ le
  decide +kernel
theorem b4_59 : Blocked tgt 6 s4_59 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s4_59 6 _ le
  decide +kernel
theorem b4_60 : Blocked tgt 6 s4_60 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_60 6 _ le
  decide +kernel
theorem b4_61 : Blocked tgt 6 s4_61 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_61 6 _ le
  decide +kernel
theorem b4_62 : Blocked tgt 6 s4_62 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s4_62 6 _ le
  decide +kernel
theorem b4_63 : Blocked tgt 6 s4_63 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_63 6 _ le
  decide +kernel
theorem b4_64 : Blocked tgt 6 s4_64 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s4_64 6 _ le
  decide +kernel
theorem b4_65 : Blocked tgt 6 s4_65 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s4_65 6 _ le
  decide +kernel
theorem b4_66 : Blocked tgt 6 s4_66 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_66 6 _ le
  decide +kernel
theorem b4_67 : Blocked tgt 6 s4_67 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s4_67 6 _ le
  decide +kernel
theorem b4_68 : Blocked tgt 6 s4_68 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s4_68 6 _ le
  decide +kernel
theorem b4_69 : Blocked tgt 6 s4_69 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s4_69 6 _ le
  decide +kernel
theorem b4_70 : Blocked tgt 6 s4_70 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s4_70 6 _ le
  decide +kernel
end ThetaCert
