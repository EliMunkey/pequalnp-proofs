import ThetaAlias
import ThetaL4S1
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1944 : Blocked tgt 7 s3_1944 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s3_1944 7 _ le
  decide +kernel
theorem b3_1945 : Blocked tgt 7 s3_1945 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1945 7 _ le
  decide +kernel
theorem b3_1946 : Blocked tgt 7 s3_1946 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1946 7 _ le
  decide +kernel
theorem b3_1947 : Blocked tgt 7 s3_1947 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1947 7 _ le
  decide +kernel
theorem b3_1948 : Blocked tgt 7 s3_1948 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1948 7 _ le
  decide +kernel
theorem b3_1949 : Blocked tgt 7 s3_1949 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(3,true))] s3_1949 7 _ le
  decide +kernel
theorem b3_1950 : Blocked tgt 7 s3_1950 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1950 7 _ le
  decide +kernel
theorem b3_1951 : Blocked tgt 7 s3_1951 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1951 7 _ le
  decide +kernel
theorem b3_1952 : Blocked tgt 7 s3_1952 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,true))] s3_1952 7 _ le
  decide +kernel
theorem b3_1953 : Blocked tgt 7 s3_1953 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b3_1954 : Blocked tgt 7 s3_1954 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_1954 7 _ le
  decide +kernel
theorem b3_1955 : Blocked tgt 7 s3_1955 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_1955 7 _ le
  decide +kernel
theorem b3_1956 : Blocked tgt 7 s3_1956 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s3_1956 7 _ le
  decide +kernel
theorem b3_1957 : Blocked tgt 7 s3_1957 := by
  apply node_sound (nxt := [s4_66])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_66
theorem b3_1958 : Blocked tgt 7 s3_1958 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1958 7 _ le
  decide +kernel
theorem b3_1959 : Blocked tgt 7 s3_1959 := by
  apply node_sound (nxt := [s4_67])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_67
theorem b3_1960 : Blocked tgt 7 s3_1960 := by
  apply node_sound (nxt := [a2407,a2408])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b4_44
    · exact via sym1 fix1 (by decide +kernel) b4_65
theorem b3_1961 : Blocked tgt 7 s3_1961 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1961 7 _ le
  decide +kernel
theorem b3_1962 : Blocked tgt 7 s3_1962 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1962 7 _ le
  decide +kernel
theorem b3_1963 : Blocked tgt 7 s3_1963 := by
  apply node_sound (nxt := [a2409,s4_68])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) b4_70
    · exact b4_68
theorem b3_1964 : Blocked tgt 7 s3_1964 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [(false,(1,true),(0,true))] s3_1964 7 _ le
  decide +kernel
theorem b3_1965 : Blocked tgt 7 s3_1965 := by
  apply node_sound (nxt := [a2410])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym1 fix1 (by decide +kernel) b4_70
theorem b3_1966 : Blocked tgt 7 s3_1966 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1966 7 _ le
  decide +kernel
theorem b3_1967 : Blocked tgt 7 s3_1967 := by
  apply node_sound (nxt := [a2411])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact via sym1 fix1 (by decide +kernel) b4_69
end ThetaCert
