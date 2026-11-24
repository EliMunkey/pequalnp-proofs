import D9Data
import D9L2S0
import D9L2S1
import D9L2S2
import D9L2S3
import D9L2S4
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
theorem b1_24 : Blocked tgt 8 s1_24 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s1_24 8 _ le
  decide +kernel
theorem b1_25 : Blocked tgt 8 s1_25 := by
  apply node_sound (nxt := [s2_0,s2_1,s2_4,s2_9,s2_17,s2_25,s2_28,s2_38,s2_43,s2_47,s2_48,s2_49,s2_50,s2_51,s2_52,s2_53,s2_55,s2_56,s2_57,s2_94,s2_96,s2_102,s2_114,s2_115,s2_116,s2_117,s2_127,s2_129,s2_134,s2_139,s2_144])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_0
    · exact b2_1
    · exact b2_4
    · exact b2_9
    · exact b2_17
    · exact b2_25
    · exact b2_28
    · exact b2_38
    · exact b2_43
    · exact b2_47
    · exact b2_48
    · exact b2_49
    · exact b2_50
    · exact b2_51
    · exact b2_52
    · exact b2_53
    · exact b2_55
    · exact b2_56
    · exact b2_57
    · exact b2_94
    · exact b2_96
    · exact b2_102
    · exact b2_114
    · exact b2_115
    · exact b2_116
    · exact b2_117
    · exact b2_127
    · exact b2_129
    · exact b2_134
    · exact b2_139
    · exact b2_144
theorem b1_26 : Blocked tgt 8 s1_26 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_26 8 _ le
  decide +kernel
theorem b1_27 : Blocked tgt 8 s1_27 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_27 8 _ le
  decide +kernel
theorem b1_28 : Blocked tgt 8 s1_28 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_28 8 _ le
  decide +kernel
theorem b1_29 : Blocked tgt 8 s1_29 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_29 8 _ le
  decide +kernel
theorem b1_30 : Blocked tgt 8 s1_30 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s1_30 8 _ le
  decide +kernel
theorem b1_31 : Blocked tgt 8 s1_31 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s1_31 8 _ le
  decide +kernel
theorem b1_32 : Blocked tgt 8 s1_32 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_32 8 _ le
  decide +kernel
theorem b1_33 : Blocked tgt 8 s1_33 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_33 8 _ le
  decide +kernel
theorem b1_34 : Blocked tgt 8 s1_34 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_34 8 _ le
  decide +kernel
theorem b1_35 : Blocked tgt 8 s1_35 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_35 8 _ le
  decide +kernel
end Deleted191Cost9
