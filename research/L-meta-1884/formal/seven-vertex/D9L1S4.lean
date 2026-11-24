import D9Data
import D9L2S0
import D9L2S1
import D9L2S2
import D9L2S3
import D9L2S4
import D9L2S5
import D9L2S6
import D9L2S7
import D9L2S8
import D9L2S9
import D9L2S10
import D9L2S11
import D9L2S12
import D9L2S13
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b1_48 : Blocked tgt 8 s1_48 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s1_48 8 _ le
  decide +kernel
theorem b1_49 : Blocked tgt 8 s1_49 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_49 8 _ le
  decide +kernel
theorem b1_50 : Blocked tgt 8 s1_50 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_50 8 _ le
  decide +kernel
theorem b1_51 : Blocked tgt 8 s1_51 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_51 8 _ le
  decide +kernel
theorem b1_52 : Blocked tgt 8 s1_52 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_52 8 _ le
  decide +kernel
theorem b1_53 : Blocked tgt 8 s1_53 := by
  apply node_sound (nxt := [s2_0,s2_6,s2_12,s2_13,s2_20,s2_21,s2_30,s2_46,s2_58,s2_59,s2_60,s2_61,s2_62,s2_63,s2_66,s2_67,s2_81,s2_84,s2_90,s2_91,s2_108,s2_109,s2_110,s2_111,s2_112,s2_128,s2_131,s2_136,s2_141,s2_146,s2_152,s2_153,s2_156])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_0
    · exact b2_6
    · exact b2_12
    · exact b2_13
    · exact b2_20
    · exact b2_21
    · exact b2_30
    · exact b2_46
    · exact b2_58
    · exact b2_59
    · exact b2_60
    · exact b2_61
    · exact b2_62
    · exact b2_63
    · exact b2_66
    · exact b2_67
    · exact b2_81
    · exact b2_84
    · exact b2_90
    · exact b2_91
    · exact b2_108
    · exact b2_109
    · exact b2_110
    · exact b2_111
    · exact b2_112
    · exact b2_128
    · exact b2_131
    · exact b2_136
    · exact b2_141
    · exact b2_146
    · exact b2_152
    · exact b2_153
    · exact b2_156
theorem b1_54 : Blocked tgt 8 s1_54 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_54 8 _ le
  decide +kernel
theorem b1_55 : Blocked tgt 8 s1_55 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_55 8 _ le
  decide +kernel
theorem b1_56 : Blocked tgt 8 s1_56 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_56 8 _ le
  decide +kernel
theorem b1_57 : Blocked tgt 8 s1_57 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_57 8 _ le
  decide +kernel
theorem b1_58 : Blocked tgt 8 s1_58 := by
  apply node_sound (nxt := [s2_0,s2_3,s2_7,s2_14,s2_15,s2_22,s2_23,s2_27,s2_31,s2_38,s2_39,s2_40,s2_41,s2_42,s2_44,s2_45,s2_68,s2_70,s2_72,s2_73,s2_74,s2_85,s2_87,s2_92,s2_93,s2_105,s2_106,s2_107,s2_119,s2_120,s2_121,s2_122,s2_128,s2_132,s2_137,s2_142,s2_147,s2_149,s2_150,s2_151,s2_156,s2_157,s2_158])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_0
    · exact b2_3
    · exact b2_7
    · exact b2_14
    · exact b2_15
    · exact b2_22
    · exact b2_23
    · exact b2_27
    · exact b2_31
    · exact b2_38
    · exact b2_39
    · exact b2_40
    · exact b2_41
    · exact b2_42
    · exact b2_44
    · exact b2_45
    · exact b2_68
    · exact b2_70
    · exact b2_72
    · exact b2_73
    · exact b2_74
    · exact b2_85
    · exact b2_87
    · exact b2_92
    · exact b2_93
    · exact b2_105
    · exact b2_106
    · exact b2_107
    · exact b2_119
    · exact b2_120
    · exact b2_121
    · exact b2_122
    · exact b2_128
    · exact b2_132
    · exact b2_137
    · exact b2_142
    · exact b2_147
    · exact b2_149
    · exact b2_150
    · exact b2_151
    · exact b2_156
    · exact b2_157
    · exact b2_158
theorem b1_59 : Blocked tgt 8 s1_59 := by
  apply node_sound (nxt := [s2_0,s2_5,s2_8,s2_16,s2_24,s2_29,s2_32,s2_33,s2_34,s2_35,s2_36,s2_37,s2_54,s2_55,s2_69,s2_71,s2_86,s2_88,s2_95,s2_103,s2_104,s2_123,s2_124,s2_125,s2_126,s2_128,s2_133,s2_138,s2_143,s2_148,s2_149,s2_154,s2_155])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_0
    · exact b2_5
    · exact b2_8
    · exact b2_16
    · exact b2_24
    · exact b2_29
    · exact b2_32
    · exact b2_33
    · exact b2_34
    · exact b2_35
    · exact b2_36
    · exact b2_37
    · exact b2_54
    · exact b2_55
    · exact b2_69
    · exact b2_71
    · exact b2_86
    · exact b2_88
    · exact b2_95
    · exact b2_103
    · exact b2_104
    · exact b2_123
    · exact b2_124
    · exact b2_125
    · exact b2_126
    · exact b2_128
    · exact b2_133
    · exact b2_138
    · exact b2_143
    · exact b2_148
    · exact b2_149
    · exact b2_154
    · exact b2_155
end Deleted191Cost9
