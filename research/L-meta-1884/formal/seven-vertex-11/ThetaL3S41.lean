import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_984 : Blocked tgt 7 s3_984 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_984 7 _ le
  decide +kernel
theorem b3_985 : Blocked tgt 7 s3_985 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_985 7 _ le
  decide +kernel
theorem b3_986 : Blocked tgt 7 s3_986 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_986 7 _ le
  decide +kernel
theorem b3_987 : Blocked tgt 7 s3_987 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_988 : Blocked tgt 7 s3_988 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s3_988 7 _ le
  decide +kernel
theorem b3_989 : Blocked tgt 7 s3_989 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_989 7 _ le
  decide +kernel
theorem b3_990 : Blocked tgt 7 s3_990 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,false))] s3_990 7 _ le
  decide +kernel
theorem b3_991 : Blocked tgt 7 s3_991 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,false))] s3_991 7 _ le
  decide +kernel
theorem b3_992 : Blocked tgt 7 s3_992 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,false))] s3_992 7 _ le
  decide +kernel
theorem b3_993 : Blocked tgt 7 s3_993 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,false))] s3_993 7 _ le
  decide +kernel
theorem b3_994 : Blocked tgt 7 s3_994 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_994 7 _ le
  decide +kernel
theorem b3_995 : Blocked tgt 7 s3_995 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_995 7 _ le
  decide +kernel
theorem b3_996 : Blocked tgt 7 s3_996 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_996 7 _ le
  decide +kernel
theorem b3_997 : Blocked tgt 7 s3_997 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_997 7 _ le
  decide +kernel
theorem b3_998 : Blocked tgt 7 s3_998 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s3_998 7 _ le
  decide +kernel
theorem b3_999 : Blocked tgt 7 s3_999 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s3_999 7 _ le
  decide +kernel
theorem b3_1000 : Blocked tgt 7 s3_1000 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,false))] s3_1000 7 _ le
  decide +kernel
theorem b3_1001 : Blocked tgt 7 s3_1001 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(4,false))] s3_1001 7 _ le
  decide +kernel
theorem b3_1002 : Blocked tgt 7 s3_1002 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_1002 7 _ le
  decide +kernel
theorem b3_1003 : Blocked tgt 7 s3_1003 := by
  intro m le c
  apply rejects_sound extra14 i6 5 tgt small14 hot14 [] s3_1003 7 _ le
  decide +kernel
theorem b3_1004 : Blocked tgt 7 s3_1004 := by
  intro m le c
  apply rejects_sound extra78 i5 4 tgt small78 hot78 [] s3_1004 7 _ le
  decide +kernel
theorem b3_1005 : Blocked tgt 7 s3_1005 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1006 : Blocked tgt 7 s3_1006 := by
  apply node_sound (nxt := [s4_64])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_64
theorem b3_1007 : Blocked tgt 7 s3_1007 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(2,true),(5,true)),(false,(2,true),(0,true))] s3_1007 7 _ le
  decide +kernel
end ThetaCert
