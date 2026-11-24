import ThetaAlias
import ThetaL4S0
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1056 : Blocked tgt 7 s3_1056 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1056 7 _ le
  decide +kernel
theorem b3_1057 : Blocked tgt 7 s3_1057 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s3_1057 7 _ le
  decide +kernel
theorem b3_1058 : Blocked tgt 7 s3_1058 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(1,true))] s3_1058 7 _ le
  decide +kernel
theorem b3_1059 : Blocked tgt 7 s3_1059 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1060 : Blocked tgt 7 s3_1060 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(0,true))] s3_1060 7 _ le
  decide +kernel
theorem b3_1061 : Blocked tgt 7 s3_1061 := by
  apply node_sound (nxt := [a2386,s4_21])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_64
    · exact b4_21
theorem b3_1062 : Blocked tgt 7 s3_1062 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(2,true))] s3_1062 7 _ le
  decide +kernel
theorem b3_1063 : Blocked tgt 7 s3_1063 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,true),(2,true))] s3_1063 7 _ le
  decide +kernel
theorem b3_1064 : Blocked tgt 7 s3_1064 := by
  apply node_sound (nxt := [s4_22])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_22
theorem b3_1065 : Blocked tgt 7 s3_1065 := by
  apply node_sound (nxt := [s4_20])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_20
theorem b3_1066 : Blocked tgt 7 s3_1066 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1066 7 _ le
  decide +kernel
theorem b3_1067 : Blocked tgt 7 s3_1067 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(0,true))] s3_1067 7 _ le
  decide +kernel
theorem b3_1068 : Blocked tgt 7 s3_1068 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(1,false),(5,true))] s3_1068 7 _ le
  decide +kernel
theorem b3_1069 : Blocked tgt 7 s3_1069 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1069 7 _ le
  decide +kernel
theorem b3_1070 : Blocked tgt 7 s3_1070 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1070 7 _ le
  decide +kernel
theorem b3_1071 : Blocked tgt 7 s3_1071 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1071 7 _ le
  decide +kernel
theorem b3_1072 : Blocked tgt 7 s3_1072 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1072 7 _ le
  decide +kernel
theorem b3_1073 : Blocked tgt 7 s3_1073 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1073 7 _ le
  decide +kernel
theorem b3_1074 : Blocked tgt 7 s3_1074 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(0,true),(1,true))] s3_1074 7 _ le
  decide +kernel
theorem b3_1075 : Blocked tgt 7 s3_1075 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1075 7 _ le
  decide +kernel
theorem b3_1076 : Blocked tgt 7 s3_1076 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1076 7 _ le
  decide +kernel
theorem b3_1077 : Blocked tgt 7 s3_1077 := by
  apply node_sound (nxt := [s4_25])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_25
theorem b3_1078 : Blocked tgt 7 s3_1078 := by
  apply node_sound (nxt := [s4_40])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_40
theorem b3_1079 : Blocked tgt 7 s3_1079 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
end ThetaCert
