import ThetaAlias
import ThetaL4S2
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b3_1872 : Blocked tgt 7 s3_1872 := by
  intro m le c
  apply rejects_sound tree6 i6 6 tgt small6 hot6 [] s3_1872 7 _ le
  decide +kernel
theorem b3_1873 : Blocked tgt 7 s3_1873 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1873 7 _ le
  decide +kernel
theorem b3_1874 : Blocked tgt 7 s3_1874 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1874 7 _ le
  decide +kernel
theorem b3_1875 : Blocked tgt 7 s3_1875 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s3_1875 7 _ le
  decide +kernel
theorem b3_1876 : Blocked tgt 7 s3_1876 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1876 7 _ le
  decide +kernel
theorem b3_1877 : Blocked tgt 7 s3_1877 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1877 7 _ le
  decide +kernel
theorem b3_1878 : Blocked tgt 7 s3_1878 := by
  intro m le c
  apply rejects_sound extra15 i6 5 tgt small15 hot15 [] s3_1878 7 _ le
  decide +kernel
theorem b3_1879 : Blocked tgt 7 s3_1879 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s3_1879 7 _ le
  decide +kernel
theorem b3_1880 : Blocked tgt 7 s3_1880 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(3,true))] s3_1880 7 _ le
  decide +kernel
theorem b3_1881 : Blocked tgt 7 s3_1881 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(3,true))] s3_1881 7 _ le
  decide +kernel
theorem b3_1882 : Blocked tgt 7 s3_1882 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1882 7 _ le
  decide +kernel
theorem b3_1883 : Blocked tgt 7 s3_1883 := by
  intro m le c
  apply rejects_sound extra31 i5 4 tgt small31 hot31 [] s3_1883 7 _ le
  decide +kernel
theorem b3_1884 : Blocked tgt 7 s3_1884 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1884 7 _ le
  decide +kernel
theorem b3_1885 : Blocked tgt 7 s3_1885 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1885 7 _ le
  decide +kernel
theorem b3_1886 : Blocked tgt 7 s3_1886 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1886 7 _ le
  decide +kernel
theorem b3_1887 : Blocked tgt 7 s3_1887 := by
  apply node_sound (nxt := [s4_51,s4_54,a2405,a2406])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_51
    · exact b4_54
    · exact via sym1 fix1 (by decide +kernel) b4_54
    · exact via sym1 fix1 (by decide +kernel) b4_51
theorem b3_1888 : Blocked tgt 7 s3_1888 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1888 7 _ le
  decide +kernel
theorem b3_1889 : Blocked tgt 7 s3_1889 := by
  apply node_sound (nxt := [s4_57])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_57
theorem b3_1890 : Blocked tgt 7 s3_1890 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1890 7 _ le
  decide +kernel
theorem b3_1891 : Blocked tgt 7 s3_1891 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_1891 7 _ le
  decide +kernel
theorem b3_1892 : Blocked tgt 7 s3_1892 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_1892 7 _ le
  decide +kernel
theorem b3_1893 : Blocked tgt 7 s3_1893 := by
  apply node_sound (nxt := [s4_58])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b4_58
theorem b3_1894 : Blocked tgt 7 s3_1894 := by
  intro m le c
  apply rejects_sound extra28 i5 4 tgt small28 hot28 [] s3_1894 7 _ le
  decide +kernel
theorem b3_1895 : Blocked tgt 7 s3_1895 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(2,true))] s3_1895 7 _ le
  decide +kernel
end ThetaCert
