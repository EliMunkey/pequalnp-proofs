import D9Data
import D9L4S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b3_12 : Blocked tgt 6 s3_12 := by
  apply node_sound (nxt := [s4_0,s4_1,s4_4])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_0
    · exact b4_1
    · exact b4_4
theorem b3_13 : Blocked tgt 6 s3_13 := by
  apply node_sound (nxt := [s4_0,s4_2,s4_6])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_0
    · exact b4_2
    · exact b4_6
theorem b3_14 : Blocked tgt 6 s3_14 := by
  apply node_sound (nxt := [s4_1,s4_3,s4_7])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_1
    · exact b4_3
    · exact b4_7
theorem b3_15 : Blocked tgt 6 s3_15 := by
  apply node_sound (nxt := [s4_2,s4_3,s4_5])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl
    · exact b4_2
    · exact b4_3
    · exact b4_5
theorem b3_16 : Blocked tgt 6 s3_16 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,false),(1,false))] s3_16 6 _ le
  decide +kernel
theorem b3_17 : Blocked tgt 6 s3_17 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_17 6 _ le
  decide +kernel
theorem b3_18 : Blocked tgt 6 s3_18 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_19 : Blocked tgt 6 s3_19 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_20 : Blocked tgt 6 s3_20 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_21 : Blocked tgt 6 s3_21 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_22 : Blocked tgt 6 s3_22 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_22 6 _ le
  decide +kernel
theorem b3_23 : Blocked tgt 6 s3_23 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,false),(1,false))] s3_23 6 _ le
  decide +kernel
end Deleted191Cost9
