import ThetaAlias
import ThetaL4S0
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_600 : Blocked tgt 7 s3_600 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(1,true))] s3_600 7 _ le
  decide +kernel
theorem b3_601 : Blocked tgt 7 s3_601 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s3_601 7 _ le
  decide +kernel
theorem b3_602 : Blocked tgt 7 s3_602 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,false))] s3_602 7 _ le
  decide +kernel
theorem b3_603 : Blocked tgt 7 s3_603 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,true))] s3_603 7 _ le
  decide +kernel
theorem b3_604 : Blocked tgt 7 s3_604 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_604 7 _ le
  decide +kernel
theorem b3_605 : Blocked tgt 7 s3_605 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_605 7 _ le
  decide +kernel
theorem b3_606 : Blocked tgt 7 s3_606 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true))] s3_606 7 _ le
  decide +kernel
theorem b3_607 : Blocked tgt 7 s3_607 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_607 7 _ le
  decide +kernel
theorem b3_608 : Blocked tgt 7 s3_608 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(4,true))] s3_608 7 _ le
  decide +kernel
theorem b3_609 : Blocked tgt 7 s3_609 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(3,true))] s3_609 7 _ le
  decide +kernel
theorem b3_610 : Blocked tgt 7 s3_610 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(1,true))] s3_610 7 _ le
  decide +kernel
theorem b3_611 : Blocked tgt 7 s3_611 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,true))] s3_611 7 _ le
  decide +kernel
theorem b3_612 : Blocked tgt 7 s3_612 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,false))] s3_612 7 _ le
  decide +kernel
theorem b3_613 : Blocked tgt 7 s3_613 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_613 7 _ le
  decide +kernel
theorem b3_614 : Blocked tgt 7 s3_614 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_614 7 _ le
  decide +kernel
theorem b3_615 : Blocked tgt 7 s3_615 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s3_615 7 _ le
  decide +kernel
theorem b3_616 : Blocked tgt 7 s3_616 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s3_616 7 _ le
  decide +kernel
theorem b3_617 : Blocked tgt 7 s3_617 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_617 7 _ le
  decide +kernel
theorem b3_618 : Blocked tgt 7 s3_618 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_618 7 _ le
  decide +kernel
theorem b3_619 : Blocked tgt 7 s3_619 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_619 7 _ le
  decide +kernel
theorem b3_620 : Blocked tgt 7 s3_620 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(4,true))] s3_620 7 _ le
  decide +kernel
theorem b3_621 : Blocked tgt 7 s3_621 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,false),(4,true))] s3_621 7 _ le
  decide +kernel
theorem b3_622 : Blocked tgt 7 s3_622 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,false),(3,true))] s3_622 7 _ le
  decide +kernel
theorem b3_623 : Blocked tgt 7 s3_623 := by
  apply node_sound (nxt := [s4_1,s4_2])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_1
    · exact b4_2
end ThetaCert
