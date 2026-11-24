import M189States
import M189L2S0
import M189L2S1
import M189L2S2
import M189L2S3
open PetersenLayerCheck
namespace M189Certificate
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem b1_30 : Blocked t 6 s1_30 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_31 : Blocked t 6 s1_31 := by
  apply node_sound (nxt := [s2_35,s2_56])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_35
    · exact b2_56
theorem b1_32 : Blocked t 6 s1_32 := by
  apply node_sound (nxt := [s2_26,s2_29,s2_33,s2_34,s2_57,s2_63,s2_77,s2_84])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_26
    · exact b2_29
    · exact b2_33
    · exact b2_34
    · exact b2_57
    · exact b2_63
    · exact b2_77
    · exact b2_84
theorem b1_33 : Blocked t 6 s1_33 := by
  apply node_sound (nxt := [s2_25,s2_28,s2_30,s2_32,s2_58,s2_70,s2_78,s2_85])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_25
    · exact b2_28
    · exact b2_30
    · exact b2_32
    · exact b2_58
    · exact b2_70
    · exact b2_78
    · exact b2_85
theorem b1_34 : Blocked t 6 s1_34 := by
  apply node_sound (nxt := [s2_27,s2_79])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_27
    · exact b2_79
theorem b1_35 : Blocked t 6 s1_35 := by
  apply node_sound (nxt := [s2_15,s2_22,s2_23,s2_24,s2_59,s2_64,s2_71,s2_91])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_15
    · exact b2_22
    · exact b2_23
    · exact b2_24
    · exact b2_59
    · exact b2_64
    · exact b2_71
    · exact b2_91
theorem b1_36 : Blocked t 6 s1_36 := by
  apply node_sound (nxt := [s2_21,s2_65])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_21
    · exact b2_65
theorem b1_37 : Blocked t 6 s1_37 := by
  apply node_sound (nxt := [s2_18,s2_72])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_18
    · exact b2_72
theorem b1_38 : Blocked t 6 s1_38 := by
  apply node_sound (nxt := [s2_14,s2_16,s2_17,s2_19,s2_66,s2_73,s2_80,s2_92])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_14
    · exact b2_16
    · exact b2_17
    · exact b2_19
    · exact b2_66
    · exact b2_73
    · exact b2_80
    · exact b2_92
theorem b1_39 : Blocked t 6 s1_39 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_40 : Blocked t 6 s1_40 := by
  apply node_sound (nxt := [s2_9,s2_10,s2_12,s2_13,s2_60,s2_67,s2_86,s2_93])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_9
    · exact b2_10
    · exact b2_12
    · exact b2_13
    · exact b2_60
    · exact b2_67
    · exact b2_86
    · exact b2_93
theorem b1_41 : Blocked t 6 s1_41 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_42 : Blocked t 6 s1_42 := by
  apply node_sound (nxt := [s2_8,s2_94])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_8
    · exact b2_94
theorem b1_43 : Blocked t 6 s1_43 := by
  apply node_sound (nxt := [s2_7,s2_49])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_7
    · exact b2_49
theorem b1_44 : Blocked t 6 s1_44 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_45 : Blocked t 6 s1_45 := by
  apply node_sound (nxt := [s2_6,s2_87])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_6
    · exact b2_87
theorem b1_46 : Blocked t 6 s1_46 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_47 : Blocked t 6 s1_47 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_48 : Blocked t 6 s1_48 := by
  apply node_sound (nxt := [s2_11,s2_48])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_11
    · exact b2_48
theorem b1_49 : Blocked t 6 s1_49 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_50 : Blocked t 6 s1_50 := by
  apply node_sound (nxt := [s2_1,s2_2,s2_3,s2_4,s2_74,s2_81,s2_88,s2_95])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_1
    · exact b2_2
    · exact b2_3
    · exact b2_4
    · exact b2_74
    · exact b2_81
    · exact b2_88
    · exact b2_95
theorem b1_51 : Blocked t 6 s1_51 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_52 : Blocked t 6 s1_52 := by
  apply node_sound (nxt := [s2_0,s2_53])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_0
    · exact b2_53
theorem b1_53 : Blocked t 6 s1_53 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_54 : Blocked t 6 s1_54 := by
  apply node_sound (nxt := [s2_31,s2_38])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_31
    · exact b2_38
theorem b1_55 : Blocked t 6 s1_55 := by
  apply node_sound (nxt := [s2_5,s2_51])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_5
    · exact b2_51
theorem b1_56 : Blocked t 6 s1_56 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_57 : Blocked t 6 s1_57 := by
  apply node_sound (nxt := [s2_20,s2_43])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · exact b2_20
    · exact b2_43
theorem b1_58 : Blocked t 6 s1_58 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
theorem b1_59 : Blocked t 6 s1_59 := by
  apply node_sound (nxt := [])
  · rfl
  · intro R h
    simp at h
end M189Certificate
