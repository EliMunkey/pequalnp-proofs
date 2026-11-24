import ThetaAlias
import ThetaL3S1
import ThetaL3S2
import ThetaL3S7
import ThetaL3S9
import ThetaL3S55
import ThetaL3S63
import ThetaL3S68
import ThetaL3S72
import ThetaL3S73
import ThetaL3S76
import ThetaL3S78
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_144 : Blocked tgt 8 s2_144 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_144 8 _ le
  decide +kernel
theorem b2_145 : Blocked tgt 8 s2_145 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_145 8 _ le
  decide +kernel
theorem b2_146 : Blocked tgt 8 s2_146 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_146 8 _ le
  decide +kernel
theorem b2_147 : Blocked tgt 8 s2_147 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_147 8 _ le
  decide +kernel
theorem b2_148 : Blocked tgt 8 s2_148 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_148 8 _ le
  decide +kernel
theorem b2_149 : Blocked tgt 8 s2_149 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_149 8 _ le
  decide +kernel
theorem b2_150 : Blocked tgt 8 s2_150 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_150 8 _ le
  decide +kernel
theorem b2_151 : Blocked tgt 8 s2_151 := by
  apply node_sound (nxt := [a906,s3_1889,s3_168,s3_60,a907,a908,s3_223])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) b3_1326
    · exact b3_1889
    · exact b3_168
    · exact b3_60
    · exact via sym3 fix3 (by decide +kernel) b3_1515
    · exact via sym2 fix2 (by decide +kernel) b3_1529
    · exact b3_223
theorem b2_152 : Blocked tgt 8 s2_152 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_152 8 _ le
  decide +kernel
theorem b2_153 : Blocked tgt 8 s2_153 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_153 8 _ le
  decide +kernel
theorem b2_154 : Blocked tgt 8 s2_154 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_154 8 _ le
  decide +kernel
theorem b2_155 : Blocked tgt 8 s2_155 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_155 8 _ le
  decide +kernel
theorem b2_156 : Blocked tgt 8 s2_156 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_156 8 _ le
  decide +kernel
theorem b2_157 : Blocked tgt 8 s2_157 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_157 8 _ le
  decide +kernel
theorem b2_158 : Blocked tgt 8 s2_158 := by
  apply node_sound (nxt := [s3_1646,a909,s3_171,s3_35,a910,s3_1758])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1646
    · exact via sym1 fix1 (by decide +kernel) b3_1824
    · exact b3_171
    · exact b3_35
    · exact via sym1 fix1 (by decide +kernel) b3_1733
    · exact b3_1758
theorem b2_159 : Blocked tgt 8 s2_159 := by
  apply node_sound (nxt := [s3_172,s3_32,a911,s3_1774])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_172
    · exact b3_32
    · exact via sym1 fix1 (by decide +kernel) b3_1734
    · exact b3_1774
theorem b2_160 : Blocked tgt 8 s2_160 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_160 8 _ le
  decide +kernel
theorem b2_161 : Blocked tgt 8 s2_161 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_161 8 _ le
  decide +kernel
theorem b2_162 : Blocked tgt 8 s2_162 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_162 8 _ le
  decide +kernel
theorem b2_163 : Blocked tgt 8 s2_163 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_163 8 _ le
  decide +kernel
theorem b2_164 : Blocked tgt 8 s2_164 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_164 8 _ le
  decide +kernel
theorem b2_165 : Blocked tgt 8 s2_165 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_165 8 _ le
  decide +kernel
theorem b2_166 : Blocked tgt 8 s2_166 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s2_166 8 _ le
  decide +kernel
theorem b2_167 : Blocked tgt 8 s2_167 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(3,true))] s2_167 8 _ le
  decide +kernel
end ThetaCert
