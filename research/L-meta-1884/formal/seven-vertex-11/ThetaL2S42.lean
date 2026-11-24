import ThetaAlias
import ThetaL3S0
import ThetaL3S1
import ThetaL3S2
import ThetaL3S3
import ThetaL3S4
import ThetaL3S5
import ThetaL3S6
import ThetaL3S8
import ThetaL3S9
import ThetaL3S11
import ThetaL3S12
import ThetaL3S15
import ThetaL3S16
import ThetaL3S18
import ThetaL3S19
import ThetaL3S20
import ThetaL3S21
import ThetaL3S22
import ThetaL3S23
import ThetaL3S24
import ThetaL3S25
import ThetaL3S26
import ThetaL3S29
import ThetaL3S30
import ThetaL3S33
import ThetaL3S34
import ThetaL3S35
import ThetaL3S36
import ThetaL3S37
import ThetaL3S38
import ThetaL3S39
import ThetaL3S40
import ThetaL3S41
import ThetaL3S42
import ThetaL3S43
import ThetaL3S44
import ThetaL3S47
import ThetaL3S48
import ThetaL3S49
import ThetaL3S50
import ThetaL3S51
import ThetaL3S52
import ThetaL3S53
import ThetaL3S54
import ThetaL3S55
import ThetaL3S56
import ThetaL3S59
import ThetaL3S60
import ThetaL3S61
import ThetaL3S63
import ThetaL3S64
import ThetaL3S65
import ThetaL3S66
import ThetaL3S67
import ThetaL3S68
import ThetaL3S69
import ThetaL3S72
import ThetaL3S73
import ThetaL3S74
import ThetaL3S75
import ThetaL3S76
import ThetaL3S77
import ThetaL3S78
import ThetaL3S79
import ThetaL3S80
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_1008 : Blocked tgt 8 s2_1008 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1008 8 _ le
  decide +kernel
theorem b2_1009 : Blocked tgt 8 s2_1009 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_1009 8 _ le
  decide +kernel
theorem b2_1010 : Blocked tgt 8 s2_1010 := by
  intro m le c
  apply rejects_sound extra12 i6 5 tgt small12 hot12 [] s2_1010 8 _ le
  decide +kernel
theorem b2_1011 : Blocked tgt 8 s2_1011 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_1011 8 _ le
  decide +kernel
theorem b2_1012 : Blocked tgt 8 s2_1012 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1012 8 _ le
  decide +kernel
theorem b2_1013 : Blocked tgt 8 s2_1013 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_1013 8 _ le
  decide +kernel
theorem b2_1014 : Blocked tgt 8 s2_1014 := by
  apply node_sound (nxt := [s3_3,a2046,a2047,s3_1474,a2048,s3_1181,s3_1797,a2049,a2050,s3_996,s3_1798,a2051,a2052,s3_463,a2053,a2054,a2055,a2056,a2057,a2058,a2059,a2060,a2061,a2062,s3_1813,a2063,a1790,a2064,s3_724,a2065,a2066])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym3 fix3 (by decide +kernel) b3_994
    · exact via sym3 fix3 (by decide +kernel) b3_989
    · exact b3_1474
    · exact via sym2 fix2 (by decide +kernel) b3_14
    · exact b3_1181
    · exact b3_1797
    · exact via sym3 fix3 (by decide +kernel) b3_1348
    · exact via sym2 fix2 (by decide +kernel) b3_13
    · exact b3_996
    · exact b3_1798
    · exact via sym1 fix1 (by decide +kernel) b3_567
    · exact via sym1 fix1 (by decide +kernel) b3_564
    · exact b3_463
    · exact via sym1 fix1 (by decide +kernel) b3_1879
    · exact via sym3 fix3 (by decide +kernel) b3_464
    · exact via sym2 fix2 (by decide +kernel) b3_1880
    · exact via sym2 fix2 (by decide +kernel) b3_1661
    · exact via sym2 fix2 (by decide +kernel) b3_1662
    · exact via sym2 fix2 (by decide +kernel) b3_1660
    · exact via sym2 fix2 (by decide +kernel) b3_15
    · exact via sym3 fix3 (by decide +kernel) b3_726
    · exact via sym3 fix3 (by decide +kernel) b3_727
    · exact via sym3 fix3 (by decide +kernel) b3_728
    · exact b3_1813
    · exact via sym2 fix2 (by decide +kernel) b3_591
    · exact via sym2 fix2 (by decide +kernel) b3_587
    · exact via sym1 fix1 (by decide +kernel) b3_1658
    · exact b3_724
    · exact via sym2 fix2 (by decide +kernel) b3_16
    · exact via sym3 fix3 (by decide +kernel) b3_1815
theorem b2_1015 : Blocked tgt 8 s2_1015 := by
  apply node_sound (nxt := [a2067,a1953,s3_1347,a2068,a2069,s3_1797,s3_3,s3_1180,s3_1177,a2070,a2071,a2072,a2073,s3_997,a2043,a2074,a2075,a2076,a2077,a2078,s3_1814,a2079,a2080,a2081,s3_725,a2082,a2083])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_954
    · exact via sym1 fix1 (by decide +kernel) b3_1865
    · exact b3_1347
    · exact via sym1 fix1 (by decide +kernel) b3_17
    · exact via sym3 fix3 (by decide +kernel) b3_997
    · exact b3_1797
    · exact b3_3
    · exact b3_1180
    · exact b3_1177
    · exact via sym1 fix1 (by decide +kernel) b3_954
    · exact via sym2 fix2 (by decide +kernel) b3_1865
    · exact via sym3 fix3 (by decide +kernel) b3_1347
    · exact via sym2 fix2 (by decide +kernel) b3_17
    · exact b3_997
    · exact via sym3 fix3 (by decide +kernel) b3_1797
    · exact via sym1 fix1 (by decide +kernel) b3_576
    · exact via sym1 fix1 (by decide +kernel) b3_573
    · exact via sym2 fix2 (by decide +kernel) b3_1659
    · exact via sym2 fix2 (by decide +kernel) b3_18
    · exact via sym3 fix3 (by decide +kernel) b3_725
    · exact b3_1814
    · exact via sym2 fix2 (by decide +kernel) b3_576
    · exact via sym2 fix2 (by decide +kernel) b3_573
    · exact via sym1 fix1 (by decide +kernel) b3_1659
    · exact b3_725
    · exact via sym1 fix1 (by decide +kernel) b3_18
    · exact via sym3 fix3 (by decide +kernel) b3_1814
theorem b2_1016 : Blocked tgt 8 s2_1016 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s2_1016 8 _ le
  decide +kernel
theorem b2_1017 : Blocked tgt 8 s2_1017 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s2_1017 8 _ le
  decide +kernel
theorem b2_1018 : Blocked tgt 8 s2_1018 := by
  intro m le c
  apply rejects_sound extra13 i6 5 tgt small13 hot13 [] s2_1018 8 _ le
  decide +kernel
theorem b2_1019 : Blocked tgt 8 s2_1019 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1019 8 _ le
  decide +kernel
theorem b2_1020 : Blocked tgt 8 s2_1020 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_1020 8 _ le
  decide +kernel
theorem b2_1021 : Blocked tgt 8 s2_1021 := by
  apply node_sound (nxt := [s3_3,a2084,a2085,s3_1475,a2086,s3_1188,s3_1809,a2087,a2088,s3_1005,s3_1811,s3_1625,a2089,a2090,s3_1813,a2091,a2092,a2093,a2094,a2095,s3_731,a2096,a2097])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_3
    · exact via sym2 fix2 (by decide +kernel) b3_1011
    · exact via sym2 fix2 (by decide +kernel) b3_1008
    · exact b3_1475
    · exact via sym2 fix2 (by decide +kernel) b3_33
    · exact b3_1188
    · exact b3_1809
    · exact via sym2 fix2 (by decide +kernel) b3_1360
    · exact via sym2 fix2 (by decide +kernel) b3_32
    · exact b3_1005
    · exact b3_1811
    · exact b3_1625
    · exact via sym2 fix2 (by decide +kernel) b3_34
    · exact via sym1 fix1 (by decide +kernel) b3_731
    · exact b3_1813
    · exact via sym3 fix3 (by decide +kernel) b3_522
    · exact via sym3 fix3 (by decide +kernel) b3_518
    · exact via sym2 fix2 (by decide +kernel) b3_522
    · exact via sym2 fix2 (by decide +kernel) b3_518
    · exact via sym1 fix1 (by decide +kernel) b3_1625
    · exact b3_731
    · exact via sym3 fix3 (by decide +kernel) b3_34
    · exact via sym1 fix1 (by decide +kernel) b3_1813
theorem b2_1022 : Blocked tgt 8 s2_1022 := by
  apply node_sound (nxt := [a2098,s3_1946,a2099,a2100,a2101,a2102,s3_1355,s3_1354,s3_1353,a2103,a2104,a2105,a2106,s3_1809,a2107,a2108,a2109,s3_1958,s3_3,s3_1187,s3_1183,s3_290,a2110,s3_950,a2111,a2112,a2113,a2114,a2115,s3_1006,s3_1812,s3_1548,a2116,s3_1626,a2117,a2118,s3_1814,a2119,a2120,a2121,a2122,a2123,a2124,a2125,s3_732,a2126,a2127])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_853
    · exact b3_1946
    · exact via sym2 fix2 (by decide +kernel) b3_893
    · exact via sym3 fix3 (by decide +kernel) b3_1877
    · exact via sym3 fix3 (by decide +kernel) b3_893
    · exact via sym2 fix2 (by decide +kernel) b3_1877
    · exact b3_1355
    · exact b3_1354
    · exact b3_1353
    · exact via sym2 fix2 (by decide +kernel) b3_36
    · exact via sym2 fix2 (by decide +kernel) b3_1015
    · exact via sym2 fix2 (by decide +kernel) b3_1016
    · exact via sym2 fix2 (by decide +kernel) b3_1014
    · exact b3_1809
    · exact via sym2 fix2 (by decide +kernel) b3_1202
    · exact via sym2 fix2 (by decide +kernel) b3_1061
    · exact via sym1 fix1 (by decide +kernel) b3_290
    · exact b3_1958
    · exact b3_3
    · exact b3_1187
    · exact b3_1183
    · exact b3_290
    · exact via sym1 fix1 (by decide +kernel) b3_1958
    · exact b3_950
    · exact via sym3 fix3 (by decide +kernel) b3_1864
    · exact via sym1 fix1 (by decide +kernel) b3_950
    · exact via sym2 fix2 (by decide +kernel) b3_1864
    · exact via sym2 fix2 (by decide +kernel) b3_1359
    · exact via sym2 fix2 (by decide +kernel) b3_35
    · exact b3_1006
    · exact b3_1812
    · exact b3_1548
    · exact via sym3 fix3 (by decide +kernel) b3_607
    · exact b3_1626
    · exact via sym2 fix2 (by decide +kernel) b3_37
    · exact via sym1 fix1 (by decide +kernel) b3_732
    · exact b3_1814
    · exact via sym3 fix3 (by decide +kernel) b3_505
    · exact via sym3 fix3 (by decide +kernel) b3_502
    · exact via sym2 fix2 (by decide +kernel) b3_505
    · exact via sym2 fix2 (by decide +kernel) b3_502
    · exact via sym1 fix1 (by decide +kernel) b3_1548
    · exact via sym2 fix2 (by decide +kernel) b3_607
    · exact via sym1 fix1 (by decide +kernel) b3_1626
    · exact b3_732
    · exact via sym3 fix3 (by decide +kernel) b3_37
    · exact via sym1 fix1 (by decide +kernel) b3_1814
theorem b2_1023 : Blocked tgt 8 s2_1023 := by
  apply node_sound (nxt := [a2128,s3_1915,s3_1356,a2129,a2130,s3_1811,s3_1476,a2131,s3_1189,s3_1812,s3_3,s3_1002,s3_999,a2132,a2133,s3_1629,s3_1628,s3_1627,a2134,a2135,a2136,a2137,s3_1815,a2138,a2139,s3_547,a2140,a2141,a2142,a2143,a2144,a2145,s3_733,s3_735,s3_734,a2146,a2147])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_828
    · exact b3_1915
    · exact b3_1356
    · exact via sym2 fix2 (by decide +kernel) b3_39
    · exact via sym2 fix2 (by decide +kernel) b3_1013
    · exact b3_1811
    · exact b3_1476
    · exact via sym2 fix2 (by decide +kernel) b3_38
    · exact b3_1189
    · exact b3_1812
    · exact b3_3
    · exact b3_1002
    · exact b3_999
    · exact via sym1 fix1 (by decide +kernel) b3_547
    · exact via sym2 fix2 (by decide +kernel) b3_1881
    · exact b3_1629
    · exact b3_1628
    · exact b3_1627
    · exact via sym2 fix2 (by decide +kernel) b3_40
    · exact via sym1 fix1 (by decide +kernel) b3_733
    · exact via sym1 fix1 (by decide +kernel) b3_734
    · exact via sym1 fix1 (by decide +kernel) b3_735
    · exact b3_1815
    · exact via sym3 fix3 (by decide +kernel) b3_488
    · exact via sym3 fix3 (by decide +kernel) b3_485
    · exact b3_547
    · exact via sym3 fix3 (by decide +kernel) b3_1881
    · exact via sym2 fix2 (by decide +kernel) b3_488
    · exact via sym2 fix2 (by decide +kernel) b3_485
    · exact via sym1 fix1 (by decide +kernel) b3_1629
    · exact via sym1 fix1 (by decide +kernel) b3_1627
    · exact via sym1 fix1 (by decide +kernel) b3_1628
    · exact b3_733
    · exact b3_735
    · exact b3_734
    · exact via sym3 fix3 (by decide +kernel) b3_40
    · exact via sym1 fix1 (by decide +kernel) b3_1815
theorem b2_1024 : Blocked tgt 8 s2_1024 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1024 8 _ le
  decide +kernel
theorem b2_1025 : Blocked tgt 8 s2_1025 := by
  apply node_sound (nxt := [s3_1193,s3_1049,a2148,s3_1525,s3_1230,s3_800,a2149,s3_1542,s3_1251,a2150,a2151,s3_1746,s3_1291,a2152,a2153,a2154,a2155,a2156,a2157,a2158,a2159,s3_164,a2160,s3_1831,a2161,s3_848,a2162,a1073,s3_1432,a2163,s3_1131,s3_1755,a2164,a2165,a2166,a2167,a2168,a2169,a2170,a2171,a2172,s3_237,a2173,s3_1833,a2174,a2175,s3_886,s3_1771,a2176,a2177,s3_942,a2178,a2179,a2180,a2181,a2182,a2183,s3_367,a2184,s3_1835,s3_1545,a2185,a2186,s3_1781,s3_1600,a2187,a2188,s3_1789,s3_1641,s3_389,a2189,s3_1837,a2190,a2191,a2192,s3_1799,a2193,s3_391,a2194,s3_1839,a2195,s3_393,a2196,s3_1841])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1193
    · exact b3_1049
    · exact via sym2 fix2 (by decide +kernel) b3_849
    · exact b3_1525
    · exact b3_1230
    · exact b3_800
    · exact via sym2 fix2 (by decide +kernel) b3_801
    · exact b3_1542
    · exact b3_1251
    · exact via sym1 fix1 (by decide +kernel) b3_207
    · exact via sym2 fix2 (by decide +kernel) b3_943
    · exact b3_1746
    · exact b3_1291
    · exact via sym3 fix3 (by decide +kernel) b3_374
    · exact via sym2 fix2 (by decide +kernel) b3_887
    · exact via sym2 fix2 (by decide +kernel) b3_1772
    · exact via sym1 fix1 (by decide +kernel) b3_1304
    · exact via sym2 fix2 (by decide +kernel) b3_373
    · exact via sym3 fix3 (by decide +kernel) b3_888
    · exact via sym3 fix3 (by decide +kernel) b3_1773
    · exact via sym1 fix1 (by decide +kernel) b3_1280
    · exact b3_164
    · exact via sym3 fix3 (by decide +kernel) b3_945
    · exact b3_1831
    · exact via sym2 fix2 (by decide +kernel) b3_1194
    · exact b3_848
    · exact via sym2 fix2 (by decide +kernel) b3_1050
    · exact via sym2 fix2 (by decide +kernel) b3_1527
    · exact b3_1432
    · exact via sym1 fix1 (by decide +kernel) b3_273
    · exact b3_1131
    · exact b3_1755
    · exact via sym2 fix2 (by decide +kernel) b3_1433
    · exact via sym3 fix3 (by decide +kernel) b3_272
    · exact via sym2 fix2 (by decide +kernel) b3_1132
    · exact via sym2 fix2 (by decide +kernel) b3_1756
    · exact via sym3 fix3 (by decide +kernel) b3_1434
    · exact via sym2 fix2 (by decide +kernel) b3_271
    · exact via sym3 fix3 (by decide +kernel) b3_1133
    · exact via sym3 fix3 (by decide +kernel) b3_1757
    · exact via sym1 fix1 (by decide +kernel) b3_1460
    · exact b3_237
    · exact via sym1 fix1 (by decide +kernel) b3_1154
    · exact b3_1833
    · exact via sym2 fix2 (by decide +kernel) b3_1292
    · exact via sym1 fix1 (by decide +kernel) b3_375
    · exact b3_886
    · exact b3_1771
    · exact via sym2 fix2 (by decide +kernel) b3_1252
    · exact via sym3 fix3 (by decide +kernel) b3_206
    · exact b3_942
    · exact via sym2 fix2 (by decide +kernel) b3_1747
    · exact via sym3 fix3 (by decide +kernel) b3_1253
    · exact via sym2 fix2 (by decide +kernel) b3_205
    · exact via sym1 fix1 (by decide +kernel) b3_958
    · exact via sym3 fix3 (by decide +kernel) b3_1748
    · exact via sym3 fix3 (by decide +kernel) b3_1300
    · exact b3_367
    · exact via sym1 fix1 (by decide +kernel) b3_911
    · exact b3_1835
    · exact b3_1545
    · exact via sym3 fix3 (by decide +kernel) b3_613
    · exact via sym1 fix1 (by decide +kernel) b3_614
    · exact b3_1781
    · exact b3_1600
    · exact via sym2 fix2 (by decide +kernel) b3_538
    · exact via sym1 fix1 (by decide +kernel) b3_550
    · exact b3_1789
    · exact b3_1641
    · exact b3_389
    · exact via sym1 fix1 (by decide +kernel) b3_470
    · exact b3_1837
    · exact via sym2 fix2 (by decide +kernel) b3_1632
    · exact via sym2 fix2 (by decide +kernel) b3_447
    · exact via sym3 fix3 (by decide +kernel) b3_448
    · exact b3_1799
    · exact via sym2 fix2 (by decide +kernel) b3_1614
    · exact b3_391
    · exact via sym3 fix3 (by decide +kernel) b3_559
    · exact b3_1839
    · exact via sym3 fix3 (by decide +kernel) b3_1573
    · exact b3_393
    · exact via sym2 fix2 (by decide +kernel) b3_632
    · exact b3_1841
theorem b2_1026 : Blocked tgt 8 s2_1026 := by
  apply node_sound (nxt := [s3_1203,s3_1063,s3_830,a2197,a2198,a2199,a2200,a2201,a2202,a2203,s3_97,a2204,s3_854,a2205,a2206,a2207,a2208,a2209,a2210,a2211,s3_128,a2212,a2213,a2214,a2215,s3_1873,a2216,s3_103,a2217,s3_1864,a2218,s3_1865,a2219,a2220,a2221,s3_150,a2222,a2223,s3_1867,s3_1851,s3_1853,s3_1852])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1203
    · exact b3_1063
    · exact b3_830
    · exact via sym2 fix2 (by decide +kernel) b3_1916
    · exact via sym2 fix2 (by decide +kernel) b3_378
    · exact via sym3 fix3 (by decide +kernel) b3_1921
    · exact via sym3 fix3 (by decide +kernel) b3_959
    · exact via sym3 fix3 (by decide +kernel) b3_946
    · exact via sym1 fix1 (by decide +kernel) b3_1286
    · exact via sym1 fix1 (by decide +kernel) b3_1285
    · exact b3_97
    · exact via sym3 fix3 (by decide +kernel) b3_984
    · exact b3_854
    · exact via sym2 fix2 (by decide +kernel) b3_1948
    · exact via sym3 fix3 (by decide +kernel) b3_294
    · exact via sym2 fix2 (by decide +kernel) b3_1960
    · exact via sym2 fix2 (by decide +kernel) b3_292
    · exact via sym3 fix3 (by decide +kernel) b3_1962
    · exact via sym1 fix1 (by decide +kernel) b3_1466
    · exact via sym1 fix1 (by decide +kernel) b3_1463
    · exact b3_128
    · exact via sym1 fix1 (by decide +kernel) b3_1163
    · exact via sym1 fix1 (by decide +kernel) b3_1146
    · exact via sym1 fix1 (by decide +kernel) b3_1143
    · exact via sym1 fix1 (by decide +kernel) b3_912
    · exact b3_1873
    · exact via sym3 fix3 (by decide +kernel) b3_1330
    · exact b3_103
    · exact via sym1 fix1 (by decide +kernel) b3_506
    · exact b3_1864
    · exact via sym3 fix3 (by decide +kernel) b3_578
    · exact b3_1865
    · exact via sym3 fix3 (by decide +kernel) b3_1589
    · exact via sym3 fix3 (by decide +kernel) b3_1588
    · exact via sym3 fix3 (by decide +kernel) b3_1578
    · exact b3_150
    · exact via sym2 fix2 (by decide +kernel) b3_710
    · exact via sym2 fix2 (by decide +kernel) b3_634
    · exact b3_1867
    · exact b3_1851
    · exact b3_1853
    · exact b3_1852
theorem b2_1027 : Blocked tgt 8 s2_1027 := by
  apply node_sound (nxt := [s3_831,a2224,a2225,a1965,a2226,a2227,a2228,a2229,s3_1358,s3_1357,s3_44,a2230,a2231,s3_1864,s3_894,a2232,a2233,s3_1878,a2234,s3_52,a2235,a2236,a2237,a2238,s3_1650,s3_1648,s3_141,a2239,a2240,a2241,a2242,s3_1879,a2243,s3_1866,a2244,a2245,a2246,s3_151,a2247,a2248,s3_1868,s3_1858,s3_1860,s3_1859])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_831
    · exact via sym2 fix2 (by decide +kernel) b3_1918
    · exact via sym2 fix2 (by decide +kernel) b3_957
    · exact via sym2 fix2 (by decide +kernel) b3_1887
    · exact via sym2 fix2 (by decide +kernel) b3_380
    · exact via sym3 fix3 (by decide +kernel) b3_1922
    · exact via sym3 fix3 (by decide +kernel) b3_960
    · exact via sym3 fix3 (by decide +kernel) b3_949
    · exact b3_1358
    · exact b3_1357
    · exact b3_44
    · exact via sym2 fix2 (by decide +kernel) b3_1003
    · exact via sym2 fix2 (by decide +kernel) b3_1185
    · exact b3_1864
    · exact b3_894
    · exact via sym2 fix2 (by decide +kernel) b3_1883
    · exact via sym1 fix1 (by decide +kernel) b3_913
    · exact b3_1878
    · exact via sym2 fix2 (by decide +kernel) b3_1350
    · exact b3_52
    · exact via sym2 fix2 (by decide +kernel) b3_1550
    · exact via sym1 fix1 (by decide +kernel) b3_615
    · exact via sym2 fix2 (by decide +kernel) b3_549
    · exact via sym3 fix3 (by decide +kernel) b3_1888
    · exact b3_1650
    · exact b3_1648
    · exact b3_141
    · exact via sym1 fix1 (by decide +kernel) b3_489
    · exact via sym1 fix1 (by decide +kernel) b3_459
    · exact via sym1 fix1 (by decide +kernel) b3_458
    · exact via sym3 fix3 (by decide +kernel) b3_593
    · exact b3_1879
    · exact via sym3 fix3 (by decide +kernel) b3_730
    · exact b3_1866
    · exact via sym3 fix3 (by decide +kernel) b3_1592
    · exact via sym3 fix3 (by decide +kernel) b3_1590
    · exact via sym3 fix3 (by decide +kernel) b3_1579
    · exact b3_151
    · exact via sym2 fix2 (by decide +kernel) b3_712
    · exact via sym2 fix2 (by decide +kernel) b3_729
    · exact b3_1868
    · exact b3_1858
    · exact b3_1860
    · exact b3_1859
theorem b2_1028 : Blocked tgt 8 s2_1028 := by
  apply node_sound (nxt := [s3_832,a2249,a2250,a2251,a2252,a2253,a2254,a2255,s3_22,a2256,a2257,s3_1865,s3_955,s3_1885,a2258,a946,a2259,s3_1881,a2260,s3_1866,a2261,a2262,a2263,a2264,s3_146,a2265,a2266,a2267,a2268,a2269,a2270,s3_1869,s3_1861,s3_1863,s3_1862])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_832
    · exact via sym2 fix2 (by decide +kernel) b3_1917
    · exact via sym2 fix2 (by decide +kernel) b3_379
    · exact via sym3 fix3 (by decide +kernel) b3_1923
    · exact via sym3 fix3 (by decide +kernel) b3_961
    · exact via sym3 fix3 (by decide +kernel) b3_953
    · exact via sym1 fix1 (by decide +kernel) b3_1346
    · exact via sym1 fix1 (by decide +kernel) b3_1345
    · exact b3_22
    · exact via sym2 fix2 (by decide +kernel) b3_995
    · exact via sym2 fix2 (by decide +kernel) b3_1178
    · exact b3_1865
    · exact b3_955
    · exact b3_1885
    · exact via sym2 fix2 (by decide +kernel) b3_1344
    · exact via sym3 fix3 (by decide +kernel) b3_24
    · exact via sym1 fix1 (by decide +kernel) b3_490
    · exact b3_1881
    · exact via sym1 fix1 (by decide +kernel) b3_723
    · exact b3_1866
    · exact via sym2 fix2 (by decide +kernel) b3_465
    · exact via sym3 fix3 (by decide +kernel) b3_1886
    · exact via sym2 fix2 (by decide +kernel) b3_1622
    · exact via sym2 fix2 (by decide +kernel) b3_1619
    · exact b3_146
    · exact via sym3 fix3 (by decide +kernel) b3_592
    · exact via sym3 fix3 (by decide +kernel) b3_546
    · exact via sym3 fix3 (by decide +kernel) b3_545
    · exact via sym3 fix3 (by decide +kernel) b3_1591
    · exact via sym2 fix2 (by decide +kernel) b3_711
    · exact via sym2 fix2 (by decide +kernel) b3_722
    · exact b3_1869
    · exact b3_1861
    · exact b3_1863
    · exact b3_1862
theorem b2_1029 : Blocked tgt 8 s2_1029 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_1029 8 _ le
  decide +kernel
theorem b2_1030 : Blocked tgt 8 s2_1030 := by
  apply node_sound (nxt := [s3_1204,s3_1064,a2271,s3_1873,s3_855,a2272,a2273,a2274,a2275,a2276,a2277,a2278,a2279,a2280,s3_72,a2281,a2282,s3_1925,a2283,a2284,s3_104,a2285,a2286,a2287,a2288,s3_1877,a2289,s3_83,s3_1870,s3_1872,s3_1871])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1204
    · exact b3_1064
    · exact via sym3 fix3 (by decide +kernel) b3_970
    · exact b3_1873
    · exact b3_855
    · exact via sym2 fix2 (by decide +kernel) b3_1947
    · exact via sym3 fix3 (by decide +kernel) b3_293
    · exact via sym2 fix2 (by decide +kernel) b3_1959
    · exact via sym2 fix2 (by decide +kernel) b3_291
    · exact via sym3 fix3 (by decide +kernel) b3_1961
    · exact via sym1 fix1 (by decide +kernel) b3_1147
    · exact via sym1 fix1 (by decide +kernel) b3_1144
    · exact via sym1 fix1 (by decide +kernel) b3_1469
    · exact via sym1 fix1 (by decide +kernel) b3_1467
    · exact b3_72
    · exact via sym1 fix1 (by decide +kernel) b3_1172
    · exact via sym2 fix2 (by decide +kernel) b3_221
    · exact b3_1925
    · exact via sym3 fix3 (by decide +kernel) b3_1334
    · exact via sym3 fix3 (by decide +kernel) b3_1329
    · exact b3_104
    · exact via sym1 fix1 (by decide +kernel) b3_927
    · exact via sym1 fix1 (by decide +kernel) b3_897
    · exact via sym1 fix1 (by decide +kernel) b3_890
    · exact via sym1 fix1 (by decide +kernel) b3_507
    · exact b3_1877
    · exact via sym3 fix3 (by decide +kernel) b3_1575
    · exact b3_83
    · exact b3_1870
    · exact b3_1872
    · exact b3_1871
theorem b2_1031 : Blocked tgt 8 s2_1031 := by
  apply node_sound (nxt := [a2290,a1977,a2291,s3_1878,a2292,s3_1877,s3_895,a2012,a2293,s3_1926,a2294,a2295,a2296,a2297,s3_53,s3_1012,a2298,a2299,a2300,a2301,s3_1655,s3_1652,s3_75,a2302,a2303,a2304,a2305,s3_1880,a2306,s3_84,s3_1874,s3_1876,s3_1875])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_956
    · exact via sym3 fix3 (by decide +kernel) b3_1883
    · exact via sym3 fix3 (by decide +kernel) b3_971
    · exact b3_1878
    · exact via sym2 fix2 (by decide +kernel) b3_1184
    · exact b3_1877
    · exact b3_895
    · exact via sym2 fix2 (by decide +kernel) b3_1882
    · exact via sym2 fix2 (by decide +kernel) b3_222
    · exact b3_1926
    · exact via sym1 fix1 (by decide +kernel) b3_898
    · exact via sym1 fix1 (by decide +kernel) b3_892
    · exact via sym2 fix2 (by decide +kernel) b3_1352
    · exact via sym2 fix2 (by decide +kernel) b3_1349
    · exact b3_53
    · exact b3_1012
    · exact via sym2 fix2 (by decide +kernel) b3_1549
    · exact via sym1 fix1 (by decide +kernel) b3_616
    · exact via sym2 fix2 (by decide +kernel) b3_548
    · exact via sym3 fix3 (by decide +kernel) b3_1884
    · exact b3_1655
    · exact b3_1652
    · exact b3_75
    · exact via sym1 fix1 (by decide +kernel) b3_523
    · exact via sym1 fix1 (by decide +kernel) b3_461
    · exact via sym1 fix1 (by decide +kernel) b3_460
    · exact via sym3 fix3 (by decide +kernel) b3_568
    · exact b3_1880
    · exact via sym3 fix3 (by decide +kernel) b3_1576
    · exact b3_84
    · exact b3_1874
    · exact b3_1876
    · exact b3_1875
end ThetaCert
