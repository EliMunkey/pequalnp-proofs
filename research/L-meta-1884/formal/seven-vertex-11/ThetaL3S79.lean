import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1896 : Blocked tgt 7 s3_1896 := by
  apply node_sound (nxt := [s4_52])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_52
theorem b3_1897 : Blocked tgt 7 s3_1897 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1897 7 _ le
  decide +kernel
theorem b3_1898 : Blocked tgt 7 s3_1898 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1898 7 _ le
  decide +kernel
theorem b3_1899 : Blocked tgt 7 s3_1899 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s3_1899 7 _ le
  decide +kernel
theorem b3_1900 : Blocked tgt 7 s3_1900 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1900 7 _ le
  decide +kernel
theorem b3_1901 : Blocked tgt 7 s3_1901 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1901 7 _ le
  decide +kernel
theorem b3_1902 : Blocked tgt 7 s3_1902 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1902 7 _ le
  decide +kernel
theorem b3_1903 : Blocked tgt 7 s3_1903 := by
  intro m le c
  apply rejects_sound extra23 i4 3 tgt small23 hot23 [] s3_1903 7 _ le
  decide +kernel
theorem b3_1904 : Blocked tgt 7 s3_1904 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1904 7 _ le
  decide +kernel
theorem b3_1905 : Blocked tgt 7 s3_1905 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1905 7 _ le
  decide +kernel
theorem b3_1906 : Blocked tgt 7 s3_1906 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1906 7 _ le
  decide +kernel
theorem b3_1907 : Blocked tgt 7 s3_1907 := by
  apply node_sound (nxt := [s4_59])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_59
theorem b3_1908 : Blocked tgt 7 s3_1908 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1908 7 _ le
  decide +kernel
theorem b3_1909 : Blocked tgt 7 s3_1909 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1909 7 _ le
  decide +kernel
theorem b3_1910 : Blocked tgt 7 s3_1910 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1910 7 _ le
  decide +kernel
theorem b3_1911 : Blocked tgt 7 s3_1911 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1911 7 _ le
  decide +kernel
theorem b3_1912 : Blocked tgt 7 s3_1912 := by
  intro m le c
  apply rejects_sound tree7 i6 6 tgt small7 hot7 [] s3_1912 7 _ le
  decide +kernel
theorem b3_1913 : Blocked tgt 7 s3_1913 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(0,true))] s3_1913 7 _ le
  decide +kernel
theorem b3_1914 : Blocked tgt 7 s3_1914 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1914 7 _ le
  decide +kernel
theorem b3_1915 : Blocked tgt 7 s3_1915 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1915 7 _ le
  decide +kernel
theorem b3_1916 : Blocked tgt 7 s3_1916 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1916 7 _ le
  decide +kernel
theorem b3_1917 : Blocked tgt 7 s3_1917 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1917 7 _ le
  decide +kernel
theorem b3_1918 : Blocked tgt 7 s3_1918 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1918 7 _ le
  decide +kernel
theorem b3_1919 : Blocked tgt 7 s3_1919 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(0,true))] s3_1919 7 _ le
  decide +kernel
end ThetaCert
