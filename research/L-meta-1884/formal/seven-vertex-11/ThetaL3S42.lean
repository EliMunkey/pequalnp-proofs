import ThetaAlias
import ThetaL4S0
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1008 : Blocked tgt 7 s3_1008 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1008 7 _ le
  decide +kernel
theorem b3_1009 : Blocked tgt 7 s3_1009 := by
  apply node_sound (nxt := [s4_55,s4_16])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b4_55
    · exact b4_16
theorem b3_1010 : Blocked tgt 7 s3_1010 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,false))] s3_1010 7 _ le
  decide +kernel
theorem b3_1011 : Blocked tgt 7 s3_1011 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1011 7 _ le
  decide +kernel
theorem b3_1012 : Blocked tgt 7 s3_1012 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1012 7 _ le
  decide +kernel
theorem b3_1013 : Blocked tgt 7 s3_1013 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1013 7 _ le
  decide +kernel
theorem b3_1014 : Blocked tgt 7 s3_1014 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1014 7 _ le
  decide +kernel
theorem b3_1015 : Blocked tgt 7 s3_1015 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1016 : Blocked tgt 7 s3_1016 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_1016 7 _ le
  decide +kernel
theorem b3_1017 : Blocked tgt 7 s3_1017 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1017 7 _ le
  decide +kernel
theorem b3_1018 : Blocked tgt 7 s3_1018 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1018 7 _ le
  decide +kernel
theorem b3_1019 : Blocked tgt 7 s3_1019 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1019 7 _ le
  decide +kernel
theorem b3_1020 : Blocked tgt 7 s3_1020 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1020 7 _ le
  decide +kernel
theorem b3_1021 : Blocked tgt 7 s3_1021 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1021 7 _ le
  decide +kernel
theorem b3_1022 : Blocked tgt 7 s3_1022 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1022 7 _ le
  decide +kernel
theorem b3_1023 : Blocked tgt 7 s3_1023 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1023 7 _ le
  decide +kernel
theorem b3_1024 : Blocked tgt 7 s3_1024 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1024 7 _ le
  decide +kernel
theorem b3_1025 : Blocked tgt 7 s3_1025 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1025 7 _ le
  decide +kernel
theorem b3_1026 : Blocked tgt 7 s3_1026 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1026 7 _ le
  decide +kernel
theorem b3_1027 : Blocked tgt 7 s3_1027 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1027 7 _ le
  decide +kernel
theorem b3_1028 : Blocked tgt 7 s3_1028 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1028 7 _ le
  decide +kernel
theorem b3_1029 : Blocked tgt 7 s3_1029 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1029 7 _ le
  decide +kernel
theorem b3_1030 : Blocked tgt 7 s3_1030 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1030 7 _ le
  decide +kernel
theorem b3_1031 : Blocked tgt 7 s3_1031 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1031 7 _ le
  decide +kernel
end ThetaCert
