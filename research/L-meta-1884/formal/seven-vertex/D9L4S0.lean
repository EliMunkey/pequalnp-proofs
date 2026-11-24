import D9Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b4_0 : Blocked tgt 5 s4_0 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_1 : Blocked tgt 5 s4_1 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2 : Blocked tgt 5 s4_2 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3 : Blocked tgt 5 s4_3 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_4 : Blocked tgt 5 s4_4 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,false),(1,false)),(false,(0,true),(3,true))] s4_4 5 _ le
  decide +kernel
theorem b4_5 : Blocked tgt 5 s4_5 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,false),(1,false)),(false,(0,true),(1,true))] s4_5 5 _ le
  decide +kernel
theorem b4_6 : Blocked tgt 5 s4_6 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,false),(1,false)),(false,(0,true),(3,true))] s4_6 5 _ le
  decide +kernel
theorem b4_7 : Blocked tgt 5 s4_7 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,false),(1,false)),(false,(0,true),(1,true))] s4_7 5 _ le
  decide +kernel
end Deleted191Cost9
