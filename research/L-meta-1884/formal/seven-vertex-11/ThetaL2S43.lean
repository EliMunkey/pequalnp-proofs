import ThetaAlias
import ThetaL3S4
import ThetaL3S5
import ThetaL3S9
import ThetaL3S11
import ThetaL3S12
import ThetaL3S13
import ThetaL3S15
import ThetaL3S17
import ThetaL3S19
import ThetaL3S20
import ThetaL3S21
import ThetaL3S22
import ThetaL3S24
import ThetaL3S25
import ThetaL3S29
import ThetaL3S31
import ThetaL3S33
import ThetaL3S34
import ThetaL3S35
import ThetaL3S36
import ThetaL3S37
import ThetaL3S38
import ThetaL3S40
import ThetaL3S41
import ThetaL3S44
import ThetaL3S46
import ThetaL3S47
import ThetaL3S48
import ThetaL3S51
import ThetaL3S52
import ThetaL3S54
import ThetaL3S55
import ThetaL3S58
import ThetaL3S59
import ThetaL3S79
import ThetaL3S80
import ThetaL3S81
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b2_1032 : Blocked tgt 8 s2_1032 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1032 8 _ le
  decide +kernel
theorem b2_1033 : Blocked tgt 8 s2_1033 := by
  apply node_sound (nxt := [s3_1074,s3_1964,a2307,a2308,s3_1249,s3_1245,s3_747,a2309,a2310,a2311,s3_223,a2312,s3_1428,s3_1414,s3_761,s3_1114,a2313,a1298,a2314,s3_1963,s3_295,a2315,s3_1900,s3_1899,s3_1898,a2316,s3_1914,a2317,a2318])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1074
    · exact b3_1964
    · exact via sym2 fix2 (by decide +kernel) b3_814
    · exact via sym2 fix2 (by decide +kernel) b3_812
    · exact b3_1249
    · exact b3_1245
    · exact b3_747
    · exact via sym2 fix2 (by decide +kernel) b3_868
    · exact via sym1 fix1 (by decide +kernel) b3_223
    · exact via sym2 fix2 (by decide +kernel) b3_1965
    · exact b3_223
    · exact via sym3 fix3 (by decide +kernel) b3_1965
    · exact b3_1428
    · exact b3_1414
    · exact b3_761
    · exact b3_1114
    · exact via sym2 fix2 (by decide +kernel) b3_1076
    · exact via sym2 fix2 (by decide +kernel) b3_1073
    · exact via sym1 fix1 (by decide +kernel) b3_295
    · exact b3_1963
    · exact b3_295
    · exact via sym1 fix1 (by decide +kernel) b3_1963
    · exact b3_1900
    · exact b3_1899
    · exact b3_1898
    · exact via sym3 fix3 (by decide +kernel) b3_327
    · exact b3_1914
    · exact via sym2 fix2 (by decide +kernel) b3_327
    · exact via sym1 fix1 (by decide +kernel) b3_1914
theorem b2_1034 : Blocked tgt 8 s2_1034 := by
  apply node_sound (nxt := [s3_1075,s3_1965,a2319,a2320,a2321,s3_1966,s3_1305,a2322,s3_1339,s3_1337,a2323,a2324,s3_224,a2325,s3_1429,s3_1115,a2326,a2327,a2328,s3_1914,a2329,s3_1924,s3_1902,s3_1901,a2330,a2331,s3_1906,s3_1905,s3_1904,a2332,a2333,s3_1908,a2334,a2335,a1707,a2336,a1696,s3_551,a2337,a2338,s3_1915])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1075
    · exact b3_1965
    · exact via sym2 fix2 (by decide +kernel) b3_834
    · exact via sym2 fix2 (by decide +kernel) b3_825
    · exact via sym1 fix1 (by decide +kernel) b3_225
    · exact b3_1966
    · exact b3_1305
    · exact via sym3 fix3 (by decide +kernel) b3_382
    · exact b3_1339
    · exact b3_1337
    · exact via sym3 fix3 (by decide +kernel) b3_137
    · exact via sym2 fix2 (by decide +kernel) b3_917
    · exact b3_224
    · exact via sym1 fix1 (by decide +kernel) b3_1967
    · exact b3_1429
    · exact b3_1115
    · exact via sym2 fix2 (by decide +kernel) b3_1148
    · exact via sym1 fix1 (by decide +kernel) b3_1916
    · exact via sym2 fix2 (by decide +kernel) b3_1164
    · exact b3_1914
    · exact via sym1 fix1 (by decide +kernel) b3_408
    · exact b3_1924
    · exact b3_1902
    · exact b3_1901
    · exact via sym3 fix3 (by decide +kernel) b3_409
    · exact via sym2 fix2 (by decide +kernel) b3_767
    · exact b3_1906
    · exact b3_1905
    · exact b3_1904
    · exact via sym1 fix1 (by decide +kernel) b3_617
    · exact via sym1 fix1 (by decide +kernel) b3_1919
    · exact b3_1908
    · exact via sym1 fix1 (by decide +kernel) b3_713
    · exact via sym3 fix3 (by decide +kernel) b3_218
    · exact via sym3 fix3 (by decide +kernel) b3_217
    · exact via sym2 fix2 (by decide +kernel) b3_466
    · exact via sym1 fix1 (by decide +kernel) b3_1918
    · exact b3_551
    · exact via sym1 fix1 (by decide +kernel) b3_1917
    · exact via sym2 fix2 (by decide +kernel) b3_491
    · exact b3_1915
theorem b2_1035 : Blocked tgt 8 s2_1035 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1035 8 _ le
  decide +kernel
theorem b2_1036 : Blocked tgt 8 s2_1036 := by
  apply node_sound (nxt := [a2339,a2340,s3_835,a2341,a2342,a2343,s3_1335,s3_1331,a2344,a2345,a2346,a2347,a2348,a1993,s3_1940,s3_1939,a2349,a2350,s3_1943,s3_1942,s3_1941,s3_325,a2351,s3_962,a1668,s3_1944,a2352,a2353,a2354,a2355,s3_1946])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_856
    · exact via sym2 fix2 (by decide +kernel) b3_852
    · exact b3_835
    · exact via sym2 fix2 (by decide +kernel) b3_1963
    · exact via sym2 fix2 (by decide +kernel) b3_899
    · exact via sym1 fix1 (by decide +kernel) b3_1947
    · exact b3_1335
    · exact b3_1331
    · exact via sym3 fix3 (by decide +kernel) b3_106
    · exact via sym2 fix2 (by decide +kernel) b3_928
    · exact via sym2 fix2 (by decide +kernel) b3_1246
    · exact via sym2 fix2 (by decide +kernel) b3_749
    · exact via sym1 fix1 (by decide +kernel) b3_326
    · exact via sym2 fix2 (by decide +kernel) b3_1956
    · exact b3_1940
    · exact b3_1939
    · exact via sym3 fix3 (by decide +kernel) b3_423
    · exact via sym2 fix2 (by decide +kernel) b3_751
    · exact b3_1943
    · exact b3_1942
    · exact b3_1941
    · exact b3_325
    · exact via sym2 fix2 (by decide +kernel) b3_1957
    · exact b3_962
    · exact via sym1 fix1 (by decide +kernel) b3_1948
    · exact b3_1944
    · exact via sym3 fix3 (by decide +kernel) b3_618
    · exact via sym3 fix3 (by decide +kernel) b3_283
    · exact via sym3 fix3 (by decide +kernel) b3_282
    · exact via sym2 fix2 (by decide +kernel) b3_508
    · exact b3_1946
theorem b2_1037 : Blocked tgt 8 s2_1037 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_1037 8 _ le
  decide +kernel
theorem b2_1038 : Blocked tgt 8 s2_1038 := by
  apply node_sound (nxt := [a2356,a1949,a2357,a1951,a2358,s3_1959,a2359,a1277,s3_900,a2360,a2361,a2362,a2363,s3_1960,a2364,s3_1957,a2365,a2366,a2367,a2368,s3_1951,s3_1950,a2369,a2370,a2371,a2372,a2373,a2374,s3_1955,a2375,s3_1954,s3_510,a2376,a2377,s3_1958,a2378,a2379,a2380,a2381])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) b3_963
    · exact via sym3 fix3 (by decide +kernel) b3_1960
    · exact via sym2 fix2 (by decide +kernel) b3_987
    · exact via sym3 fix3 (by decide +kernel) b3_1957
    · exact via sym3 fix3 (by decide +kernel) b3_900
    · exact b3_1959
    · exact via sym1 fix1 (by decide +kernel) b3_1332
    · exact via sym2 fix2 (by decide +kernel) b3_107
    · exact b3_900
    · exact via sym3 fix3 (by decide +kernel) b3_1959
    · exact via sym2 fix2 (by decide +kernel) b3_1332
    · exact via sym1 fix1 (by decide +kernel) b3_107
    · exact via sym1 fix1 (by decide +kernel) b3_963
    · exact b3_1960
    · exact via sym1 fix1 (by decide +kernel) b3_987
    · exact b3_1957
    · exact via sym1 fix1 (by decide +kernel) b3_286
    · exact via sym1 fix1 (by decide +kernel) b3_285
    · exact via sym2 fix2 (by decide +kernel) b3_1949
    · exact via sym1 fix1 (by decide +kernel) b3_619
    · exact b3_1951
    · exact b3_1950
    · exact via sym2 fix2 (by decide +kernel) b3_118
    · exact via sym1 fix1 (by decide +kernel) b3_579
    · exact via sym3 fix3 (by decide +kernel) b3_1950
    · exact via sym3 fix3 (by decide +kernel) b3_1951
    · exact via sym2 fix2 (by decide +kernel) b3_579
    · exact via sym1 fix1 (by decide +kernel) b3_118
    · exact b3_1955
    · exact via sym3 fix3 (by decide +kernel) b3_1954
    · exact b3_1954
    · exact b3_510
    · exact via sym3 fix3 (by decide +kernel) b3_1958
    · exact via sym3 fix3 (by decide +kernel) b3_510
    · exact b3_1958
    · exact via sym2 fix2 (by decide +kernel) b3_286
    · exact via sym2 fix2 (by decide +kernel) b3_285
    · exact via sym1 fix1 (by decide +kernel) b3_1949
    · exact via sym2 fix2 (by decide +kernel) b3_619
end ThetaCert
