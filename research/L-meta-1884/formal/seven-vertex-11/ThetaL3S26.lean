import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_624 : Blocked tgt 7 s3_624 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_624 7 _ le
  decide +kernel
theorem b3_625 : Blocked tgt 7 s3_625 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(3,true))] s3_625 7 _ le
  decide +kernel
theorem b3_626 : Blocked tgt 7 s3_626 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s3_626 7 _ le
  decide +kernel
theorem b3_627 : Blocked tgt 7 s3_627 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s3_627 7 _ le
  decide +kernel
theorem b3_628 : Blocked tgt 7 s3_628 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_629 : Blocked tgt 7 s3_629 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_629 7 _ le
  decide +kernel
theorem b3_630 : Blocked tgt 7 s3_630 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(1,true))] s3_630 7 _ le
  decide +kernel
theorem b3_631 : Blocked tgt 7 s3_631 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,true))] s3_631 7 _ le
  decide +kernel
theorem b3_632 : Blocked tgt 7 s3_632 := by
  intro m le c
  apply rejects_sound extra61 i4 3 tgt small61 hot61 [] s3_632 7 _ le
  decide +kernel
theorem b3_633 : Blocked tgt 7 s3_633 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,false))] s3_633 7 _ le
  decide +kernel
theorem b3_634 : Blocked tgt 7 s3_634 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_634 7 _ le
  decide +kernel
theorem b3_635 : Blocked tgt 7 s3_635 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_635 7 _ le
  decide +kernel
theorem b3_636 : Blocked tgt 7 s3_636 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_636 7 _ le
  decide +kernel
theorem b3_637 : Blocked tgt 7 s3_637 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(4,true)),(false,(0,true),(6,true))] s3_637 7 _ le
  decide +kernel
theorem b3_638 : Blocked tgt 7 s3_638 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_638 7 _ le
  decide +kernel
theorem b3_639 : Blocked tgt 7 s3_639 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_639 7 _ le
  decide +kernel
theorem b3_640 : Blocked tgt 7 s3_640 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_640 7 _ le
  decide +kernel
theorem b3_641 : Blocked tgt 7 s3_641 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_641 7 _ le
  decide +kernel
theorem b3_642 : Blocked tgt 7 s3_642 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_642 7 _ le
  decide +kernel
theorem b3_643 : Blocked tgt 7 s3_643 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(2,false),(3,true))] s3_643 7 _ le
  decide +kernel
theorem b3_644 : Blocked tgt 7 s3_644 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_644 7 _ le
  decide +kernel
theorem b3_645 : Blocked tgt 7 s3_645 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,true)),(false,(0,true),(4,true))] s3_645 7 _ le
  decide +kernel
theorem b3_646 : Blocked tgt 7 s3_646 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_646 7 _ le
  decide +kernel
theorem b3_647 : Blocked tgt 7 s3_647 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_647 7 _ le
  decide +kernel
end ThetaCert
