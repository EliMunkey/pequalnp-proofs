import M189States
import M189L2S1
import M189L2S2
import M189L2S3
open PetersenLayerCheck
namespace M189Certificate
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem b1_0 : Blocked t 6 s1_0 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_1 : Blocked t 6 s1_1 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_2 : Blocked t 6 s1_2 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_3 : Blocked t 6 s1_3 := by
  apply node_sound (nxt := [s2_42,s2_50,s2_61,s2_82])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_42
    · exact b2_50
    · exact b2_61
    · exact b2_82
theorem b1_4 : Blocked t 6 s1_4 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_5 : Blocked t 6 s1_5 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_6 : Blocked t 6 s1_6 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_7 : Blocked t 6 s1_7 := by
  apply node_sound (nxt := [s2_37,s2_52,s2_54,s2_89])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_37
    · exact b2_52
    · exact b2_54
    · exact b2_89
theorem b1_8 : Blocked t 6 s1_8 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_9 : Blocked t 6 s1_9 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_10 : Blocked t 6 s1_10 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_11 : Blocked t 6 s1_11 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_12 : Blocked t 6 s1_12 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_13 : Blocked t 6 s1_13 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_14 : Blocked t 6 s1_14 := by
  apply node_sound (nxt := [s2_36,s2_46,s2_75,s2_90])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_36
    · exact b2_46
    · exact b2_75
    · exact b2_90
theorem b1_15 : Blocked t 6 s1_15 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_16 : Blocked t 6 s1_16 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_17 : Blocked t 6 s1_17 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_18 : Blocked t 6 s1_18 := by
  apply node_sound (nxt := [s2_41,s2_47,s2_68,s2_83])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_41
    · exact b2_47
    · exact b2_68
    · exact b2_83
theorem b1_19 : Blocked t 6 s1_19 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_20 : Blocked t 6 s1_20 := by
  apply node_sound (nxt := [s2_44,s2_45,s2_55,s2_76])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_44
    · exact b2_45
    · exact b2_55
    · exact b2_76
theorem b1_21 : Blocked t 6 s1_21 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_22 : Blocked t 6 s1_22 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_23 : Blocked t 6 s1_23 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_24 : Blocked t 6 s1_24 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_25 : Blocked t 6 s1_25 := by
  apply node_sound (nxt := [s2_39,s2_40,s2_62,s2_69])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact b2_39
    · exact b2_40
    · exact b2_62
    · exact b2_69
theorem b1_26 : Blocked t 6 s1_26 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_27 : Blocked t 6 s1_27 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_28 : Blocked t 6 s1_28 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_29 : Blocked t 6 s1_29 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
end M189Certificate
