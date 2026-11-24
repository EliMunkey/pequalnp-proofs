import D9Data
import D9L3S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_36 : Blocked tgt 7 s2_36 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_36 7 _ le
  decide +kernel
theorem b2_37 : Blocked tgt 7 s2_37 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_37 7 _ le
  decide +kernel
theorem b2_38 : Blocked tgt 7 s2_38 := by
  apply node_sound (nxt := [s3_11])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_11
theorem b2_39 : Blocked tgt 7 s2_39 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_39 7 _ le
  decide +kernel
theorem b2_40 : Blocked tgt 7 s2_40 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_40 7 _ le
  decide +kernel
theorem b2_41 : Blocked tgt 7 s2_41 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_41 7 _ le
  decide +kernel
theorem b2_42 : Blocked tgt 7 s2_42 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_42 7 _ le
  decide +kernel
theorem b2_43 : Blocked tgt 7 s2_43 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_43 7 _ le
  decide +kernel
theorem b2_44 : Blocked tgt 7 s2_44 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_44 7 _ le
  decide +kernel
theorem b2_45 : Blocked tgt 7 s2_45 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_45 7 _ le
  decide +kernel
theorem b2_46 : Blocked tgt 7 s2_46 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_46 7 _ le
  decide +kernel
theorem b2_47 : Blocked tgt 7 s2_47 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_47 7 _ le
  decide +kernel
end Deleted191Cost9
