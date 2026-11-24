import D9Data
import D9L3S1
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_84 : Blocked tgt 7 s2_84 := by
  apply node_sound (nxt := [s3_17])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    exact mem ▸ b3_17
theorem b2_85 : Blocked tgt 7 s2_85 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_85 7 _ le
  decide +kernel
theorem b2_86 : Blocked tgt 7 s2_86 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_86 7 _ le
  decide +kernel
theorem b2_87 : Blocked tgt 7 s2_87 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_87 7 _ le
  decide +kernel
theorem b2_88 : Blocked tgt 7 s2_88 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b2_89 : Blocked tgt 7 s2_89 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_89 7 _ le
  decide +kernel
theorem b2_90 : Blocked tgt 7 s2_90 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_90 7 _ le
  decide +kernel
theorem b2_91 : Blocked tgt 7 s2_91 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_91 7 _ le
  decide +kernel
theorem b2_92 : Blocked tgt 7 s2_92 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_92 7 _ le
  decide +kernel
theorem b2_93 : Blocked tgt 7 s2_93 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s2_93 7 _ le
  decide +kernel
theorem b2_94 : Blocked tgt 7 s2_94 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_94 7 _ le
  decide +kernel
theorem b2_95 : Blocked tgt 7 s2_95 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s2_95 7 _ le
  decide +kernel
end Deleted191Cost9
