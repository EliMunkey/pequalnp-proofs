import D9Data
import D9L2S0
import D9L2S1
import D9L2S2
import D9L2S3
import D9L2S5
import D9L2S6
import D9L2S7
import D9L2S8
import D9L2S9
import D9L2S10
import D9L2S11
import D9L2S12
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b1_36 : Blocked tgt 8 s1_36 := by
  apply node_sound (nxt := [s2_0,s2_2,s2_10,s2_11,s2_18,s2_19,s2_26,s2_38,s2_64,s2_65,s2_75,s2_76,s2_77,s2_78,s2_79,s2_80,s2_82,s2_83,s2_84,s2_89,s2_97,s2_98,s2_99,s2_100,s2_101,s2_113,s2_118,s2_130,s2_135,s2_140,s2_145])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_0
    · exact b2_2
    · exact b2_10
    · exact b2_11
    · exact b2_18
    · exact b2_19
    · exact b2_26
    · exact b2_38
    · exact b2_64
    · exact b2_65
    · exact b2_75
    · exact b2_76
    · exact b2_77
    · exact b2_78
    · exact b2_79
    · exact b2_80
    · exact b2_82
    · exact b2_83
    · exact b2_84
    · exact b2_89
    · exact b2_97
    · exact b2_98
    · exact b2_99
    · exact b2_100
    · exact b2_101
    · exact b2_113
    · exact b2_118
    · exact b2_130
    · exact b2_135
    · exact b2_140
    · exact b2_145
theorem b1_37 : Blocked tgt 8 s1_37 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s1_37 8 _ le
  decide +kernel
theorem b1_38 : Blocked tgt 8 s1_38 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_38 8 _ le
  decide +kernel
theorem b1_39 : Blocked tgt 8 s1_39 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_39 8 _ le
  decide +kernel
theorem b1_40 : Blocked tgt 8 s1_40 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_40 8 _ le
  decide +kernel
theorem b1_41 : Blocked tgt 8 s1_41 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_41 8 _ le
  decide +kernel
theorem b1_42 : Blocked tgt 8 s1_42 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s1_42 8 _ le
  decide +kernel
theorem b1_43 : Blocked tgt 8 s1_43 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s1_43 8 _ le
  decide +kernel
theorem b1_44 : Blocked tgt 8 s1_44 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_44 8 _ le
  decide +kernel
theorem b1_45 : Blocked tgt 8 s1_45 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_45 8 _ le
  decide +kernel
theorem b1_46 : Blocked tgt 8 s1_46 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_46 8 _ le
  decide +kernel
theorem b1_47 : Blocked tgt 8 s1_47 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_47 8 _ le
  decide +kernel
end Deleted191Cost9
