import D9Data
import D9L3S1
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_48 : Blocked tgt 7 s2_48 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_48 7 _ le
  decide +kernel
theorem b2_49 : Blocked tgt 7 s2_49 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_49 7 _ le
  decide +kernel
theorem b2_50 : Blocked tgt 7 s2_50 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_50 7 _ le
  decide +kernel
theorem b2_51 : Blocked tgt 7 s2_51 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_51 7 _ le
  decide +kernel
theorem b2_52 : Blocked tgt 7 s2_52 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_52 7 _ le
  decide +kernel
theorem b2_53 : Blocked tgt 7 s2_53 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_53 7 _ le
  decide +kernel
theorem b2_54 : Blocked tgt 7 s2_54 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_54 7 _ le
  decide +kernel
theorem b2_55 : Blocked tgt 7 s2_55 := by
  apply node_sound (nxt := [s3_17])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_17
theorem b2_56 : Blocked tgt 7 s2_56 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,true))] s2_56 7 _ le
  decide +kernel
theorem b2_57 : Blocked tgt 7 s2_57 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(2,true))] s2_57 7 _ le
  decide +kernel
theorem b2_58 : Blocked tgt 7 s2_58 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b2_59 : Blocked tgt 7 s2_59 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_59 7 _ le
  decide +kernel
end Deleted191Cost9
