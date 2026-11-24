import ThetaAlias
import ThetaL3S0
import ThetaL3S2
import ThetaL3S3
import ThetaL3S9
import ThetaL3S11
import ThetaL3S12
import ThetaL3S13
import ThetaL3S15
import ThetaL3S16
import ThetaL3S17
import ThetaL3S19
import ThetaL3S21
import ThetaL3S24
import ThetaL3S26
import ThetaL3S29
import ThetaL3S30
import ThetaL3S34
import ThetaL3S37
import ThetaL3S38
import ThetaL3S40
import ThetaL3S41
import ThetaL3S44
import ThetaL3S47
import ThetaL3S48
import ThetaL3S49
import ThetaL3S50
import ThetaL3S53
import ThetaL3S54
import ThetaL3S55
import ThetaL3S61
import ThetaL3S65
import ThetaL3S66
import ThetaL3S67
import ThetaL3S68
import ThetaL3S69
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S78
import ThetaL3S79
import ThetaL3S80
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_984 : Blocked tgt 8 s2_984 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_984 8 _ le
  decide +kernel
theorem b2_985 : Blocked tgt 8 s2_985 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_985 8 _ le
  decide +kernel
theorem b2_986 : Blocked tgt 8 s2_986 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s2_986 8 _ le
  decide +kernel
theorem b2_987 : Blocked tgt 8 s2_987 := by
  apply node_sound (nxt := [s3_1201,s3_1060,s3_827,a1686,s3_3,a1990,a1991,s3_1161,s3_1158,a1992,a1993,a1994,a1951,a1995,a1996,s3_929,s3_1780,a1666,a1997,a1998,a1999,a2000,a2001,a2002,a2003,a2004,s3_1787,a2005,a2006,a2007,s3_1797,a2008,s3_511,a2009,a1677])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1201
    · exact b3_1060
    · exact b3_827
    · exact via sym2 fix2 (by decide +kernel) b3_1914
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_983
    · exact via sym2 fix2 (by decide +kernel) b3_980
    · exact b3_1161
    · exact b3_1158
    · exact via sym3 fix3 (by decide +kernel) b3_289
    · exact via sym2 fix2 (by decide +kernel) b3_1956
    · exact via sym2 fix2 (by decide +kernel) b3_287
    · exact via sym3 fix3 (by decide +kernel) b3_1957
    · exact via sym2 fix2 (by decide +kernel) b3_1340
    · exact via sym1 fix1 (by decide +kernel) b3_89
    · exact b3_929
    · exact b3_1780
    · exact via sym1 fix1 (by decide +kernel) b3_324
    · exact via sym1 fix1 (by decide +kernel) b3_321
    · exact via sym2 fix2 (by decide +kernel) b3_1598
    · exact via sym2 fix2 (by decide +kernel) b3_1596
    · exact via sym2 fix2 (by decide +kernel) b3_1597
    · exact via sym3 fix3 (by decide +kernel) b3_719
    · exact via sym3 fix3 (by decide +kernel) b3_721
    · exact via sym3 fix3 (by decide +kernel) b3_720
    · exact via sym1 fix1 (by decide +kernel) b3_92
    · exact b3_1787
    · exact via sym3 fix3 (by decide +kernel) b3_1624
    · exact via sym2 fix2 (by decide +kernel) b3_595
    · exact via sym1 fix1 (by decide +kernel) b3_91
    · exact b3_1797
    · exact via sym1 fix1 (by decide +kernel) b3_1651
    · exact b3_511
    · exact via sym1 fix1 (by decide +kernel) b3_90
    · exact via sym2 fix2 (by decide +kernel) b3_1812
theorem b2_988 : Blocked tgt 8 s2_988 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_988 8 _ le
  decide +kernel
theorem b2_989 : Blocked tgt 8 s2_989 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_989 8 _ le
  decide +kernel
theorem b2_990 : Blocked tgt 8 s2_990 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_990 8 _ le
  decide +kernel
theorem b2_991 : Blocked tgt 8 s2_991 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_991 8 _ le
  decide +kernel
theorem b2_992 : Blocked tgt 8 s2_992 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_992 8 _ le
  decide +kernel
theorem b2_993 : Blocked tgt 8 s2_993 := by
  apply node_sound (nxt := [s3_1768,a2010,a2011,s3_1798])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b3_1768
    · exact via sym2 fix2 (by decide +kernel) b3_79
    · exact via sym1 fix1 (by decide +kernel) b3_79
    · exact b3_1798
theorem b2_994 : Blocked tgt 8 s2_994 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_994 8 _ le
  decide +kernel
theorem b2_995 : Blocked tgt 8 s2_995 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_995 8 _ le
  decide +kernel
theorem b2_996 : Blocked tgt 8 s2_996 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_996 8 _ le
  decide +kernel
theorem b2_997 : Blocked tgt 8 s2_997 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_997 8 _ le
  decide +kernel
theorem b2_998 : Blocked tgt 8 s2_998 := by
  apply node_sound (nxt := [a2012,s3_1654,a2013,a2014,s3_520,s3_1769,s3_74,a1235,a998])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_1882
    · exact b3_1654
    · exact via sym1 fix1 (by decide +kernel) b3_520
    · exact via sym1 fix1 (by decide +kernel) b3_1654
    · exact b3_520
    · exact b3_1769
    · exact b3_74
    · exact via sym1 fix1 (by decide +kernel) b3_74
    · exact via sym2 fix2 (by decide +kernel) b3_1807
theorem b2_999 : Blocked tgt 8 s2_999 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_999 8 _ le
  decide +kernel
theorem b2_1000 : Blocked tgt 8 s2_1000 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_1000 8 _ le
  decide +kernel
theorem b2_1001 : Blocked tgt 8 s2_1001 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1001 8 _ le
  decide +kernel
theorem b2_1002 : Blocked tgt 8 s2_1002 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(2,true),(3,true))] s2_1002 8 _ le
  decide +kernel
theorem b2_1003 : Blocked tgt 8 s2_1003 := by
  apply node_sound (nxt := [s3_3,a2015,a1898,s3_1145,a1687,s3_1473,s3_1472,s3_1470,a2016,s3_1176,s3_1175,s3_1173,s3_1780,a2017,a2018,s3_916,s3_910,a2019,s3_1924,a1690,a1710,s3_462,a2020,a2021,a2022,a2023,a2024,a2025,a2026,a2027,s3_1788,a2028,a2029,a2030,s3_1798,a2031,s3_524,a2032,a1982])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_974
    · exact via sym2 fix2 (by decide +kernel) b3_969
    · exact b3_1145
    · exact via sym1 fix1 (by decide +kernel) b3_1873
    · exact b3_1473
    · exact b3_1472
    · exact b3_1470
    · exact via sym1 fix1 (by decide +kernel) b3_64
    · exact b3_1176
    · exact b3_1175
    · exact b3_1173
    · exact b3_1780
    · exact via sym2 fix2 (by decide +kernel) b3_1303
    · exact via sym1 fix1 (by decide +kernel) b3_372
    · exact b3_916
    · exact b3_910
    · exact via sym3 fix3 (by decide +kernel) b3_220
    · exact b3_1924
    · exact via sym1 fix1 (by decide +kernel) b3_407
    · exact via sym1 fix1 (by decide +kernel) b3_404
    · exact b3_462
    · exact via sym1 fix1 (by decide +kernel) b3_1878
    · exact via sym2 fix2 (by decide +kernel) b3_1595
    · exact via sym2 fix2 (by decide +kernel) b3_1593
    · exact via sym2 fix2 (by decide +kernel) b3_1594
    · exact via sym3 fix3 (by decide +kernel) b3_715
    · exact via sym3 fix3 (by decide +kernel) b3_717
    · exact via sym3 fix3 (by decide +kernel) b3_716
    · exact via sym1 fix1 (by decide +kernel) b3_67
    · exact b3_1788
    · exact via sym3 fix3 (by decide +kernel) b3_1623
    · exact via sym2 fix2 (by decide +kernel) b3_594
    · exact via sym1 fix1 (by decide +kernel) b3_66
    · exact b3_1798
    · exact via sym1 fix1 (by decide +kernel) b3_1656
    · exact b3_524
    · exact via sym1 fix1 (by decide +kernel) b3_65
    · exact via sym2 fix2 (by decide +kernel) b3_1811
theorem b2_1004 : Blocked tgt 8 s2_1004 := by
  apply node_sound (nxt := [s3_1289,a1076,a2033,s3_1780,s3_3,s3_1169,s3_1166,s3_925,s3_922,a2034,a2035,a2036,a2037,a2038,a2039,a2040,a2041,a2042,a2043,a2044,s3_525,a2045,a1989])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1289
    · exact via sym1 fix1 (by decide +kernel) b3_60
    · exact via sym2 fix2 (by decide +kernel) b3_988
    · exact b3_1780
    · exact b3_3
    · exact b3_1169
    · exact b3_1166
    · exact b3_925
    · exact b3_922
    · exact via sym1 fix1 (by decide +kernel) b3_422
    · exact via sym1 fix1 (by decide +kernel) b3_418
    · exact via sym2 fix2 (by decide +kernel) b3_1577
    · exact via sym3 fix3 (by decide +kernel) b3_635
    · exact via sym1 fix1 (by decide +kernel) b3_63
    · exact via sym2 fix2 (by decide +kernel) b3_1787
    · exact via sym3 fix3 (by decide +kernel) b3_1618
    · exact via sym2 fix2 (by decide +kernel) b3_580
    · exact via sym1 fix1 (by decide +kernel) b3_62
    · exact via sym3 fix3 (by decide +kernel) b3_1797
    · exact via sym1 fix1 (by decide +kernel) b3_1657
    · exact b3_525
    · exact via sym1 fix1 (by decide +kernel) b3_61
    · exact via sym2 fix2 (by decide +kernel) b3_1809
theorem b2_1005 : Blocked tgt 8 s2_1005 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1005 8 _ le
  decide +kernel
theorem b2_1006 : Blocked tgt 8 s2_1006 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1006 8 _ le
  decide +kernel
theorem b2_1007 : Blocked tgt 8 s2_1007 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1007 8 _ le
  decide +kernel
end ThetaCert
