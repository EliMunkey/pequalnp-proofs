import ThetaAlias
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S20
import ThetaL3S21
import ThetaL3S28
import ThetaL3S29
import ThetaL3S48
import ThetaL3S61
import ThetaL3S65
import ThetaL3S68
import ThetaL3S72
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S77
import ThetaL3S78
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_960 : Blocked tgt 8 s2_960 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_960 8 _ le
  decide +kernel
theorem b2_961 : Blocked tgt 8 s2_961 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_961 8 _ le
  decide +kernel
theorem b2_962 : Blocked tgt 8 s2_962 := by
  apply node_sound (nxt := [a1965,s3_1649,a1966,a1967,a1968,a1969,s3_486,s3_1742,s3_140,a1970,a978,a1971,a1972])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1887
    · exact b3_1649
    · exact via sym1 fix1 (by decide +kernel) b3_486
    · exact via sym2 fix2 (by decide +kernel) b3_1583
    · exact via sym3 fix3 (by decide +kernel) b3_696
    · exact via sym1 fix1 (by decide +kernel) b3_1649
    · exact b3_486
    · exact b3_1742
    · exact b3_140
    · exact via sym1 fix1 (by decide +kernel) b3_140
    · exact via sym2 fix2 (by decide +kernel) b3_1810
    · exact via sym3 fix3 (by decide +kernel) b3_1583
    · exact via sym2 fix2 (by decide +kernel) b3_696
theorem b2_963 : Blocked tgt 8 s2_963 := by
  apply node_sound (nxt := [s3_1465,s3_1162,s3_112,a1973,a1974,a1975,s3_1743,s3_114,a1976,a1677])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1465
    · exact b3_1162
    · exact b3_112
    · exact via sym1 fix1 (by decide +kernel) b3_1864
    · exact via sym2 fix2 (by decide +kernel) b3_1582
    · exact via sym3 fix3 (by decide +kernel) b3_695
    · exact b3_1743
    · exact b3_114
    · exact via sym1 fix1 (by decide +kernel) b3_142
    · exact via sym2 fix2 (by decide +kernel) b3_1812
theorem b2_964 : Blocked tgt 8 s2_964 := by
  apply node_sound (nxt := [a1977,s3_1653,a1978,a1979,a1980,s3_1744,s3_76,a1981,a1982])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) b3_1883
    · exact b3_1653
    · exact via sym1 fix1 (by decide +kernel) b3_519
    · exact via sym2 fix2 (by decide +kernel) b3_1581
    · exact via sym3 fix3 (by decide +kernel) b3_694
    · exact b3_1744
    · exact b3_76
    · exact via sym1 fix1 (by decide +kernel) b3_143
    · exact via sym2 fix2 (by decide +kernel) b3_1811
theorem b2_965 : Blocked tgt 8 s2_965 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_965 8 _ le
  decide +kernel
theorem b2_966 : Blocked tgt 8 s2_966 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_966 8 _ le
  decide +kernel
theorem b2_967 : Blocked tgt 8 s2_967 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_967 8 _ le
  decide +kernel
theorem b2_968 : Blocked tgt 8 s2_968 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(3,true))] s2_968 8 _ le
  decide +kernel
theorem b2_969 : Blocked tgt 8 s2_969 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_969 8 _ le
  decide +kernel
theorem b2_970 : Blocked tgt 8 s2_970 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_970 8 _ le
  decide +kernel
theorem b2_971 : Blocked tgt 8 s2_971 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_971 8 _ le
  decide +kernel
theorem b2_972 : Blocked tgt 8 s2_972 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_972 8 _ le
  decide +kernel
theorem b2_973 : Blocked tgt 8 s2_973 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_973 8 _ le
  decide +kernel
theorem b2_974 : Blocked tgt 8 s2_974 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_974 8 _ le
  decide +kernel
theorem b2_975 : Blocked tgt 8 s2_975 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_975 8 _ le
  decide +kernel
theorem b2_976 : Blocked tgt 8 s2_976 := by
  apply node_sound (nxt := [s3_1959,a1983,a1984,s3_1753,a1985,a1986,s3_1797])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1959
    · exact via sym3 fix3 (by decide +kernel) b3_1468
    · exact via sym3 fix3 (by decide +kernel) b3_1171
    · exact b3_1753
    · exact via sym2 fix2 (by decide +kernel) b3_80
    · exact via sym1 fix1 (by decide +kernel) b3_119
    · exact b3_1797
theorem b2_977 : Blocked tgt 8 s2_977 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_977 8 _ le
  decide +kernel
theorem b2_978 : Blocked tgt 8 s2_978 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_978 8 _ le
  decide +kernel
theorem b2_979 : Blocked tgt 8 s2_979 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_979 8 _ le
  decide +kernel
theorem b2_980 : Blocked tgt 8 s2_980 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_980 8 _ le
  decide +kernel
theorem b2_981 : Blocked tgt 8 s2_981 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_981 8 _ le
  decide +kernel
theorem b2_982 : Blocked tgt 8 s2_982 := by
  apply node_sound (nxt := [a1987,s3_1877,s3_1754,s3_77,a1988,a1989])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) b3_113
    · exact b3_1877
    · exact b3_1754
    · exact b3_77
    · exact via sym1 fix1 (by decide +kernel) b3_115
    · exact via sym2 fix2 (by decide +kernel) b3_1809
theorem b2_983 : Blocked tgt 8 s2_983 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_983 8 _ le
  decide +kernel
end ThetaCert
