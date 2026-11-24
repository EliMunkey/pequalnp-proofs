import M189States
import M189L1S0
import M189L1S1
open PetersenLayerCheck
namespace M189Certificate
set_option maxRecDepth 24000
set_option maxHeartbeats 0
theorem b0_0 : Blocked t 7 s0_0 := by
  apply node_sound (nxt := [s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15,s1_16,s1_17,s1_18,s1_19,s1_20,s1_21,s1_22,s1_23,s1_24,s1_25,s1_26,s1_27,s1_28,s1_29,s1_30,s1_31,s1_32,s1_33,s1_34,s1_35,s1_36,s1_37,s1_38,s1_39,s1_40,s1_41,s1_42,s1_43,s1_44,s1_45,s1_46,s1_47,s1_48,s1_49,s1_50,s1_51,s1_52,s1_53,s1_54,s1_55,s1_56,s1_57,s1_58,s1_59])
  · rfl
  · intro R h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b1_0
    · exact b1_1
    · exact b1_2
    · exact b1_3
    · exact b1_4
    · exact b1_5
    · exact b1_6
    · exact b1_7
    · exact b1_8
    · exact b1_9
    · exact b1_10
    · exact b1_11
    · exact b1_12
    · exact b1_13
    · exact b1_14
    · exact b1_15
    · exact b1_16
    · exact b1_17
    · exact b1_18
    · exact b1_19
    · exact b1_20
    · exact b1_21
    · exact b1_22
    · exact b1_23
    · exact b1_24
    · exact b1_25
    · exact b1_26
    · exact b1_27
    · exact b1_28
    · exact b1_29
    · exact b1_30
    · exact b1_31
    · exact b1_32
    · exact b1_33
    · exact b1_34
    · exact b1_35
    · exact b1_36
    · exact b1_37
    · exact b1_38
    · exact b1_39
    · exact b1_40
    · exact b1_41
    · exact b1_42
    · exact b1_43
    · exact b1_44
    · exact b1_45
    · exact b1_46
    · exact b1_47
    · exact b1_48
    · exact b1_49
    · exact b1_50
    · exact b1_51
    · exact b1_52
    · exact b1_53
    · exact b1_54
    · exact b1_55
    · exact b1_56
    · exact b1_57
    · exact b1_58
    · exact b1_59
end M189Certificate
