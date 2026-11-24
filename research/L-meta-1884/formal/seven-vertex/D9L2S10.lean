import D9Data
import D9L3S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_120 : Blocked tgt 7 s2_120 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_120 7 _ le
  decide +kernel
theorem b2_121 : Blocked tgt 7 s2_121 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_121 7 _ le
  decide +kernel
theorem b2_122 : Blocked tgt 7 s2_122 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_122 7 _ le
  decide +kernel
theorem b2_123 : Blocked tgt 7 s2_123 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_123 7 _ le
  decide +kernel
theorem b2_124 : Blocked tgt 7 s2_124 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_124 7 _ le
  decide +kernel
theorem b2_125 : Blocked tgt 7 s2_125 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_125 7 _ le
  decide +kernel
theorem b2_126 : Blocked tgt 7 s2_126 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_126 7 _ le
  decide +kernel
theorem b2_127 : Blocked tgt 7 s2_127 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_127 7 _ le
  decide +kernel
theorem b2_128 : Blocked tgt 7 s2_128 := by
  apply node_sound (nxt := [s3_2])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_2
theorem b2_129 : Blocked tgt 7 s2_129 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,true))] s2_129 7 _ le
  decide +kernel
theorem b2_130 : Blocked tgt 7 s2_130 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,false))] s2_130 7 _ le
  decide +kernel
theorem b2_131 : Blocked tgt 7 s2_131 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_131 7 _ le
  decide +kernel
end Deleted191Cost9
