import D9Data
import D9L3S0
import D9L3S1
import D9L3S2
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_96 : Blocked tgt 7 s2_96 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b2_97 : Blocked tgt 7 s2_97 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_97 7 _ le
  decide +kernel
theorem b2_98 : Blocked tgt 7 s2_98 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_98 7 _ le
  decide +kernel
theorem b2_99 : Blocked tgt 7 s2_99 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_99 7 _ le
  decide +kernel
theorem b2_100 : Blocked tgt 7 s2_100 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_100 7 _ le
  decide +kernel
theorem b2_101 : Blocked tgt 7 s2_101 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_101 7 _ le
  decide +kernel
theorem b2_102 : Blocked tgt 7 s2_102 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_102 7 _ le
  decide +kernel
theorem b2_103 : Blocked tgt 7 s2_103 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_103 7 _ le
  decide +kernel
theorem b2_104 : Blocked tgt 7 s2_104 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_104 7 _ le
  decide +kernel
theorem b2_105 : Blocked tgt 7 s2_105 := by
  apply node_sound (nxt := [s3_0,s3_1,s3_4,s3_6,s3_8,s3_10,s3_18,s3_19,s3_20,s3_21,s3_22,s3_24])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_0
    · exact b3_1
    · exact b3_4
    · exact b3_6
    · exact b3_8
    · exact b3_10
    · exact b3_18
    · exact b3_19
    · exact b3_20
    · exact b3_21
    · exact b3_22
    · exact b3_24
theorem b2_106 : Blocked tgt 7 s2_106 := by
  apply node_sound (nxt := [s3_2])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_2
theorem b2_107 : Blocked tgt 7 s2_107 := by
  apply node_sound (nxt := [s3_0,s3_1,s3_3,s3_5,s3_7,s3_9,s3_12,s3_13,s3_14,s3_15,s3_16,s3_23])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_0
    · exact b3_1
    · exact b3_3
    · exact b3_5
    · exact b3_7
    · exact b3_9
    · exact b3_12
    · exact b3_13
    · exact b3_14
    · exact b3_15
    · exact b3_16
    · exact b3_23
end Deleted191Cost9
