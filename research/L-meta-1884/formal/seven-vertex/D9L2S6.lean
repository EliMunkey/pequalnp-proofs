import D9Data
import D9L3S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_72 : Blocked tgt 7 s2_72 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b2_73 : Blocked tgt 7 s2_73 := by
  apply node_sound (nxt := [s3_11])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_11
theorem b2_74 : Blocked tgt 7 s2_74 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b2_75 : Blocked tgt 7 s2_75 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_75 7 _ le
  decide +kernel
theorem b2_76 : Blocked tgt 7 s2_76 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_76 7 _ le
  decide +kernel
theorem b2_77 : Blocked tgt 7 s2_77 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_77 7 _ le
  decide +kernel
theorem b2_78 : Blocked tgt 7 s2_78 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_78 7 _ le
  decide +kernel
theorem b2_79 : Blocked tgt 7 s2_79 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_79 7 _ le
  decide +kernel
theorem b2_80 : Blocked tgt 7 s2_80 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_80 7 _ le
  decide +kernel
theorem b2_81 : Blocked tgt 7 s2_81 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_81 7 _ le
  decide +kernel
theorem b2_82 : Blocked tgt 7 s2_82 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,false))] s2_82 7 _ le
  decide +kernel
theorem b2_83 : Blocked tgt 7 s2_83 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,false))] s2_83 7 _ le
  decide +kernel
end Deleted191Cost9
