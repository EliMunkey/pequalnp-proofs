import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1920 : Blocked tgt 7 s3_1920 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(0,true))] s3_1920 7 _ le
  decide +kernel
theorem b3_1921 : Blocked tgt 7 s3_1921 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1921 7 _ le
  decide +kernel
theorem b3_1922 : Blocked tgt 7 s3_1922 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1922 7 _ le
  decide +kernel
theorem b3_1923 : Blocked tgt 7 s3_1923 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1923 7 _ le
  decide +kernel
theorem b3_1924 : Blocked tgt 7 s3_1924 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s3_1924 7 _ le
  decide +kernel
theorem b3_1925 : Blocked tgt 7 s3_1925 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_1925 7 _ le
  decide +kernel
theorem b3_1926 : Blocked tgt 7 s3_1926 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_1926 7 _ le
  decide +kernel
theorem b3_1927 : Blocked tgt 7 s3_1927 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1927 7 _ le
  decide +kernel
theorem b3_1928 : Blocked tgt 7 s3_1928 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1928 7 _ le
  decide +kernel
theorem b3_1929 : Blocked tgt 7 s3_1929 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s3_1929 7 _ le
  decide +kernel
theorem b3_1930 : Blocked tgt 7 s3_1930 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1930 7 _ le
  decide +kernel
theorem b3_1931 : Blocked tgt 7 s3_1931 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(1,true))] s3_1931 7 _ le
  decide +kernel
theorem b3_1932 : Blocked tgt 7 s3_1932 := by
  apply node_sound (nxt := [s4_52])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_52
theorem b3_1933 : Blocked tgt 7 s3_1933 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1933 7 _ le
  decide +kernel
theorem b3_1934 : Blocked tgt 7 s3_1934 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1934 7 _ le
  decide +kernel
theorem b3_1935 : Blocked tgt 7 s3_1935 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1935 7 _ le
  decide +kernel
theorem b3_1936 : Blocked tgt 7 s3_1936 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1936 7 _ le
  decide +kernel
theorem b3_1937 : Blocked tgt 7 s3_1937 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1938 : Blocked tgt 7 s3_1938 := by
  intro m le c
  apply rejects_sound extra55 i5 4 tgt small55 hot55 [] s3_1938 7 _ le
  decide +kernel
theorem b3_1939 : Blocked tgt 7 s3_1939 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1939 7 _ le
  decide +kernel
theorem b3_1940 : Blocked tgt 7 s3_1940 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1940 7 _ le
  decide +kernel
theorem b3_1941 : Blocked tgt 7 s3_1941 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1941 7 _ le
  decide +kernel
theorem b3_1942 : Blocked tgt 7 s3_1942 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1942 7 _ le
  decide +kernel
theorem b3_1943 : Blocked tgt 7 s3_1943 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1943 7 _ le
  decide +kernel
end ThetaCert
