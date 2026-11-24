import ThetaAlias
import ThetaL4S0
import ThetaL4S1
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1032 : Blocked tgt 7 s3_1032 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_1032 7 _ le
  decide +kernel
theorem b3_1033 : Blocked tgt 7 s3_1033 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(1,false))] s3_1033 7 _ le
  decide +kernel
theorem b3_1034 : Blocked tgt 7 s3_1034 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(1,false))] s3_1034 7 _ le
  decide +kernel
theorem b3_1035 : Blocked tgt 7 s3_1035 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,false),(5,true))] s3_1035 7 _ le
  decide +kernel
theorem b3_1036 : Blocked tgt 7 s3_1036 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1036 7 _ le
  decide +kernel
theorem b3_1037 : Blocked tgt 7 s3_1037 := by
  apply node_sound (nxt := [a2383,a2384,s4_24,s4_17])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_24
    · exact via sym2 fix2 (by decide +kernel) b4_17
    · exact b4_24
    · exact b4_17
theorem b3_1038 : Blocked tgt 7 s3_1038 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,false),(5,true))] s3_1038 7 _ le
  decide +kernel
theorem b3_1039 : Blocked tgt 7 s3_1039 := by
  apply node_sound (nxt := [a2385,s4_18,s4_23])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_30
    · exact b4_18
    · exact b4_23
theorem b3_1040 : Blocked tgt 7 s3_1040 := by
  apply node_sound (nxt := [s4_37])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_37
theorem b3_1041 : Blocked tgt 7 s3_1041 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1041 7 _ le
  decide +kernel
theorem b3_1042 : Blocked tgt 7 s3_1042 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s3_1042 7 _ le
  decide +kernel
theorem b3_1043 : Blocked tgt 7 s3_1043 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1043 7 _ le
  decide +kernel
theorem b3_1044 : Blocked tgt 7 s3_1044 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s3_1044 7 _ le
  decide +kernel
theorem b3_1045 : Blocked tgt 7 s3_1045 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,false),(5,true))] s3_1045 7 _ le
  decide +kernel
theorem b3_1046 : Blocked tgt 7 s3_1046 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(1,false))] s3_1046 7 _ le
  decide +kernel
theorem b3_1047 : Blocked tgt 7 s3_1047 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1047 7 _ le
  decide +kernel
theorem b3_1048 : Blocked tgt 7 s3_1048 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1048 7 _ le
  decide +kernel
theorem b3_1049 : Blocked tgt 7 s3_1049 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1049 7 _ le
  decide +kernel
theorem b3_1050 : Blocked tgt 7 s3_1050 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(1,true),(3,true))] s3_1050 7 _ le
  decide +kernel
theorem b3_1051 : Blocked tgt 7 s3_1051 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1051 7 _ le
  decide +kernel
theorem b3_1052 : Blocked tgt 7 s3_1052 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1052 7 _ le
  decide +kernel
theorem b3_1053 : Blocked tgt 7 s3_1053 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1053 7 _ le
  decide +kernel
theorem b3_1054 : Blocked tgt 7 s3_1054 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s3_1054 7 _ le
  decide +kernel
theorem b3_1055 : Blocked tgt 7 s3_1055 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s3_1055 7 _ le
  decide +kernel
end ThetaCert
