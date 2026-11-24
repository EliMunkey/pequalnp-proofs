import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S3
import ThetaL3S5
import ThetaL3S13
import ThetaL3S17
import ThetaL3S28
import ThetaL3S29
import ThetaL3S31
import ThetaL3S33
import ThetaL3S36
import ThetaL3S40
import ThetaL3S44
import ThetaL3S45
import ThetaL3S48
import ThetaL3S51
import ThetaL3S52
import ThetaL3S58
import ThetaL3S59
import ThetaL3S61
import ThetaL3S62
import ThetaL3S63
import ThetaL3S64
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_840 : Blocked tgt 8 s2_840 := by
  apply node_sound (nxt := [s3_1076,s3_1235,s3_814,s3_1415,s3_1098,a1659,s3_865,s3_1506,s3_760,a1301,s3_1544])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1076
    · exact b3_1235
    · exact b3_814
    · exact b3_1415
    · exact b3_1098
    · exact via sym2 fix2 (by decide +kernel) b3_1247
    · exact b3_865
    · exact b3_1506
    · exact b3_760
    · exact via sym2 fix2 (by decide +kernel) b3_745
    · exact b3_1544
theorem b2_841 : Blocked tgt 8 s2_841 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_841 8 _ le
  decide +kernel
theorem b2_842 : Blocked tgt 8 s2_842 := by
  apply node_sound (nxt := [a1660,s3_1098,a1661,s3_867,s3_3,a1301])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_866
    · exact b3_1098
    · exact via sym2 fix2 (by decide +kernel) b3_1248
    · exact b3_867
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_745
theorem b2_843 : Blocked tgt 8 s2_843 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_843 8 _ le
  decide +kernel
theorem b2_844 : Blocked tgt 8 s2_844 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_844 8 _ le
  decide +kernel
theorem b2_845 : Blocked tgt 8 s2_845 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_845 8 _ le
  decide +kernel
theorem b2_846 : Blocked tgt 8 s2_846 := by
  apply node_sound (nxt := [s3_1464,s3_1159,s3_1509,a1662,s3_1512,a1663,a1406,s3_1767,s3_1522,a1664])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1464
    · exact b3_1159
    · exact b3_1509
    · exact via sym1 fix1 (by decide +kernel) b3_322
    · exact b3_1512
    · exact via sym1 fix1 (by decide +kernel) b3_127
    · exact via sym2 fix2 (by decide +kernel) b3_753
    · exact b3_1767
    · exact b3_1522
    · exact via sym3 fix3 (by decide +kernel) b3_681
theorem b2_847 : Blocked tgt 8 s2_847 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_847 8 _ le
  decide +kernel
theorem b2_848 : Blocked tgt 8 s2_848 := by
  apply node_sound (nxt := [a1665,s3_1060,s3_1159,s3_1510,a1666,s3_3,a1406,s3_1523,a1667])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_981
    · exact b3_1060
    · exact b3_1159
    · exact b3_1510
    · exact via sym1 fix1 (by decide +kernel) b3_324
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_753
    · exact b3_1523
    · exact via sym3 fix3 (by decide +kernel) b3_718
theorem b2_849 : Blocked tgt 8 s2_849 := by
  apply node_sound (nxt := [s3_1513,a1121,a1425,s3_1780])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_1513
    · exact via sym1 fix1 (by decide +kernel) b3_73
    · exact via sym2 fix2 (by decide +kernel) b3_754
    · exact b3_1780
theorem b2_850 : Blocked tgt 8 s2_850 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(0,true),(1,true))] s2_850 8 _ le
  decide +kernel
theorem b2_851 : Blocked tgt 8 s2_851 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s2_851 8 _ le
  decide +kernel
theorem b2_852 : Blocked tgt 8 s2_852 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_852 8 _ le
  decide +kernel
theorem b2_853 : Blocked tgt 8 s2_853 := by
  intro m le c
  apply rejects_sound extra97 i4 3 tgt small97 hot97 [] s2_853 8 _ le
  decide +kernel
theorem b2_854 : Blocked tgt 8 s2_854 := by
  apply node_sound (nxt := [s3_1965,a1668,s3_1514,a1669,s3_1516,a1123,a1670,a1671,s3_1521,a1672])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1965
    · exact via sym1 fix1 (by decide +kernel) b3_1948
    · exact b3_1514
    · exact via sym3 fix3 (by decide +kernel) b3_419
    · exact b3_1516
    · exact via sym3 fix3 (by decide +kernel) b3_138
    · exact via sym2 fix2 (by decide +kernel) b3_752
    · exact via sym2 fix2 (by decide +kernel) b3_1780
    · exact b3_1521
    · exact via sym1 fix1 (by decide +kernel) b3_672
theorem b2_855 : Blocked tgt 8 s2_855 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(1,true))] s2_855 8 _ le
  decide +kernel
theorem b2_856 : Blocked tgt 8 s2_856 := by
  apply node_sound (nxt := [s3_1517,a1673,a1443,s3_1797])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_1517
    · exact via sym1 fix1 (by decide +kernel) b3_26
    · exact via sym3 fix3 (by decide +kernel) b3_755
    · exact b3_1797
theorem b2_857 : Blocked tgt 8 s2_857 := by
  apply node_sound (nxt := [a1674,s3_1946,s3_1518,a1675,a1466,s3_1809])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_48
    · exact b3_1946
    · exact b3_1518
    · exact via sym2 fix2 (by decide +kernel) b3_55
    · exact via sym2 fix2 (by decide +kernel) b3_757
    · exact b3_1809
theorem b2_858 : Blocked tgt 8 s2_858 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s2_858 8 _ le
  decide +kernel
theorem b2_859 : Blocked tgt 8 s2_859 := by
  apply node_sound (nxt := [s3_1519,s3_49,a1676,a1677])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_1519
    · exact b3_49
    · exact via sym2 fix2 (by decide +kernel) b3_756
    · exact via sym2 fix2 (by decide +kernel) b3_1812
theorem b2_860 : Blocked tgt 8 s2_860 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_860 8 _ le
  decide +kernel
theorem b2_861 : Blocked tgt 8 s2_861 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_861 8 _ le
  decide +kernel
theorem b2_862 : Blocked tgt 8 s2_862 := by
  apply node_sound (nxt := [a1678,s3_1419,s3_1101,s3_1100,s3_865,s3_3,s3_760])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_865
    · exact b3_1419
    · exact b3_1101
    · exact b3_1100
    · exact b3_865
    · exact b3_3
    · exact b3_760
theorem b2_863 : Blocked tgt 8 s2_863 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(0,true),(2,true))] s2_863 8 _ le
  decide +kernel
end ThetaCert
