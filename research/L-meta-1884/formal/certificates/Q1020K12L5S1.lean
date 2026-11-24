import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b5_42 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_42 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [(false,(6,true),(5,true))] s5_42 7 _ le
  decide +kernel
theorem b5_43 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_43 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,false)),(false,(0,true),(5,true))] s5_43 7 _ le
  decide +kernel
theorem b5_44 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_44 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,false))] s5_44 7 _ le
  decide +kernel
theorem b5_45 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_45 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,false)),(false,(4,true),(0,true))] s5_45 7 _ le
  decide +kernel
theorem b5_46 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_46 := by
  intro m le c
  apply rejects_sound extra61 i6 5 tgt small61 hot61 [] s5_46 7 _ le
  decide +kernel
theorem b5_47 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_47 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s5_47 7 _ le
  decide +kernel
theorem b5_48 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_48 := by
  intro m le c
  apply rejects_sound extra92 i6 5 tgt small92 hot92 [(false,(5,true),(4,true))] s5_48 7 _ le
  decide +kernel
theorem b5_49 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_49 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,false))] s5_49 7 _ le
  decide +kernel
theorem b5_50 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_50 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s5_50 7 _ le
  decide +kernel
theorem b5_51 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_51 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s5_51 7 _ le
  decide +kernel
theorem b5_52 (theta : Extra1020K12.Theta) : Blocked tgt 7 s5_52 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(7,true),(1,true)),(false,(4,true),(2,true)),(false,(7,true),(9,true))] s5_52 7 _ le
  decide +kernel
end Orbits1020Cost12
