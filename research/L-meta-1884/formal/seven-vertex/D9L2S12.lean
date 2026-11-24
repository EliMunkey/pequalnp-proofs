import D9Data
import D9L3S1
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_144 : Blocked tgt 7 s2_144 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(2,true))] s2_144 7 _ le
  decide +kernel
theorem b2_145 : Blocked tgt 7 s2_145 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,false))] s2_145 7 _ le
  decide +kernel
theorem b2_146 : Blocked tgt 7 s2_146 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_146 7 _ le
  decide +kernel
theorem b2_147 : Blocked tgt 7 s2_147 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s2_147 7 _ le
  decide +kernel
theorem b2_148 : Blocked tgt 7 s2_148 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(2,true))] s2_148 7 _ le
  decide +kernel
theorem b2_149 : Blocked tgt 7 s2_149 := by
  apply node_sound (nxt := [s3_22])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_22
theorem b2_150 : Blocked tgt 7 s2_150 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_150 7 _ le
  decide +kernel
theorem b2_151 : Blocked tgt 7 s2_151 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s2_151 7 _ le
  decide +kernel
theorem b2_152 : Blocked tgt 7 s2_152 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_152 7 _ le
  decide +kernel
theorem b2_153 : Blocked tgt 7 s2_153 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_153 7 _ le
  decide +kernel
theorem b2_154 : Blocked tgt 7 s2_154 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s2_154 7 _ le
  decide +kernel
theorem b2_155 : Blocked tgt 7 s2_155 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(2,true))] s2_155 7 _ le
  decide +kernel
end Deleted191Cost9
