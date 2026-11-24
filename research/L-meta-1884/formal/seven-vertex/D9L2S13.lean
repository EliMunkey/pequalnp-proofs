import D9Data
import D9L3S2
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_156 : Blocked tgt 7 s2_156 := by
  apply node_sound (nxt := [s3_24])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_24
theorem b2_157 : Blocked tgt 7 s2_157 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_157 7 _ le
  decide +kernel
theorem b2_158 : Blocked tgt 7 s2_158 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s2_158 7 _ le
  decide +kernel
end Deleted191Cost9
