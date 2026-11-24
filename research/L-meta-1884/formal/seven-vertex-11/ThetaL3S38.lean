import ThetaAlias
import ThetaL4S0
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_912 : Blocked tgt 7 s3_912 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_912 7 _ le
  decide +kernel
theorem b3_913 : Blocked tgt 7 s3_913 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_913 7 _ le
  decide +kernel
theorem b3_914 : Blocked tgt 7 s3_914 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_914 7 _ le
  decide +kernel
theorem b3_915 : Blocked tgt 7 s3_915 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,false))] s3_915 7 _ le
  decide +kernel
theorem b3_916 : Blocked tgt 7 s3_916 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_916 7 _ le
  decide +kernel
theorem b3_917 : Blocked tgt 7 s3_917 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_917 7 _ le
  decide +kernel
theorem b3_918 : Blocked tgt 7 s3_918 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_918 7 _ le
  decide +kernel
theorem b3_919 : Blocked tgt 7 s3_919 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_919 7 _ le
  decide +kernel
theorem b3_920 : Blocked tgt 7 s3_920 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,false))] s3_920 7 _ le
  decide +kernel
theorem b3_921 : Blocked tgt 7 s3_921 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true)),(false,(3,true),(0,true))] s3_921 7 _ le
  decide +kernel
theorem b3_922 : Blocked tgt 7 s3_922 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s3_922 7 _ le
  decide +kernel
theorem b3_923 : Blocked tgt 7 s3_923 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(2,false))] s3_923 7 _ le
  decide +kernel
theorem b3_924 : Blocked tgt 7 s3_924 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_924 7 _ le
  decide +kernel
theorem b3_925 : Blocked tgt 7 s3_925 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_925 7 _ le
  decide +kernel
theorem b3_926 : Blocked tgt 7 s3_926 := by
  apply node_sound (nxt := [a2382,s4_14])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) b4_56
    · exact b4_14
theorem b3_927 : Blocked tgt 7 s3_927 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s3_927 7 _ le
  decide +kernel
theorem b3_928 : Blocked tgt 7 s3_928 := by
  intro m le c
  apply rejects_sound extra40 i5 4 tgt small40 hot40 [] s3_928 7 _ le
  decide +kernel
theorem b3_929 : Blocked tgt 7 s3_929 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_929 7 _ le
  decide +kernel
theorem b3_930 : Blocked tgt 7 s3_930 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_930 7 _ le
  decide +kernel
theorem b3_931 : Blocked tgt 7 s3_931 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_931 7 _ le
  decide +kernel
theorem b3_932 : Blocked tgt 7 s3_932 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_932 7 _ le
  decide +kernel
theorem b3_933 : Blocked tgt 7 s3_933 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_933 7 _ le
  decide +kernel
theorem b3_934 : Blocked tgt 7 s3_934 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_934 7 _ le
  decide +kernel
theorem b3_935 : Blocked tgt 7 s3_935 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s3_935 7 _ le
  decide +kernel
end ThetaCert
