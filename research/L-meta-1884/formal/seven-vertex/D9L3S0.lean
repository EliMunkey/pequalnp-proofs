import D9Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck
namespace Deleted191Cost9
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b3_0 : Blocked tgt 6 s3_0 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [(false,(5,false),(1,false))] s3_0 6 _ le
  decide +kernel
theorem b3_1 : Blocked tgt 6 s3_1 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,false),(1,false))] s3_1 6 _ le
  decide +kernel
theorem b3_2 : Blocked tgt 6 s3_2 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_3 : Blocked tgt 6 s3_3 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,false),(0,true))] s3_3 6 _ le
  decide +kernel
theorem b3_4 : Blocked tgt 6 s3_4 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_4 6 _ le
  decide +kernel
theorem b3_5 : Blocked tgt 6 s3_5 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true)),(false,(2,false),(0,true))] s3_5 6 _ le
  decide +kernel
theorem b3_6 : Blocked tgt 6 s3_6 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_6 6 _ le
  decide +kernel
theorem b3_7 : Blocked tgt 6 s3_7 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true)),(false,(2,false),(0,true))] s3_7 6 _ le
  decide +kernel
theorem b3_8 : Blocked tgt 6 s3_8 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_8 6 _ le
  decide +kernel
theorem b3_9 : Blocked tgt 6 s3_9 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true)),(false,(2,false),(0,true))] s3_9 6 _ le
  decide +kernel
theorem b3_10 : Blocked tgt 6 s3_10 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_10 6 _ le
  decide +kernel
theorem b3_11 : Blocked tgt 6 s3_11 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
end Deleted191Cost9
