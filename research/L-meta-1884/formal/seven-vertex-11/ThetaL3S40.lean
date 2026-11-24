import ThetaAlias
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_960 : Blocked tgt 7 s3_960 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_960 7 _ le
  decide +kernel
theorem b3_961 : Blocked tgt 7 s3_961 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_961 7 _ le
  decide +kernel
theorem b3_962 : Blocked tgt 7 s3_962 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_962 7 _ le
  decide +kernel
theorem b3_963 : Blocked tgt 7 s3_963 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s3_963 7 _ le
  decide +kernel
theorem b3_964 : Blocked tgt 7 s3_964 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_964 7 _ le
  decide +kernel
theorem b3_965 : Blocked tgt 7 s3_965 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_965 7 _ le
  decide +kernel
theorem b3_966 : Blocked tgt 7 s3_966 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_966 7 _ le
  decide +kernel
theorem b3_967 : Blocked tgt 7 s3_967 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,false))] s3_967 7 _ le
  decide +kernel
theorem b3_968 : Blocked tgt 7 s3_968 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,false))] s3_968 7 _ le
  decide +kernel
theorem b3_969 : Blocked tgt 7 s3_969 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,false),(2,true))] s3_969 7 _ le
  decide +kernel
theorem b3_970 : Blocked tgt 7 s3_970 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s3_970 7 _ le
  decide +kernel
theorem b3_971 : Blocked tgt 7 s3_971 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_972 : Blocked tgt 7 s3_972 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_972 7 _ le
  decide +kernel
theorem b3_973 : Blocked tgt 7 s3_973 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,false))] s3_973 7 _ le
  decide +kernel
theorem b3_974 : Blocked tgt 7 s3_974 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_974 7 _ le
  decide +kernel
theorem b3_975 : Blocked tgt 7 s3_975 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,false))] s3_975 7 _ le
  decide +kernel
theorem b3_976 : Blocked tgt 7 s3_976 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(3,false))] s3_976 7 _ le
  decide +kernel
theorem b3_977 : Blocked tgt 7 s3_977 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(0,true))] s3_977 7 _ le
  decide +kernel
theorem b3_978 : Blocked tgt 7 s3_978 := by
  intro m le c
  apply rejects_sound extra44 i5 4 tgt small44 hot44 [] s3_978 7 _ le
  decide +kernel
theorem b3_979 : Blocked tgt 7 s3_979 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [(false,(5,true),(0,true))] s3_979 7 _ le
  decide +kernel
theorem b3_980 : Blocked tgt 7 s3_980 := by
  intro m le c
  apply rejects_sound extra44 i5 4 tgt small44 hot44 [] s3_980 7 _ le
  decide +kernel
theorem b3_981 : Blocked tgt 7 s3_981 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(3,false))] s3_981 7 _ le
  decide +kernel
theorem b3_982 : Blocked tgt 7 s3_982 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_982 7 _ le
  decide +kernel
theorem b3_983 : Blocked tgt 7 s3_983 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s3_983 7 _ le
  decide +kernel
end ThetaCert
