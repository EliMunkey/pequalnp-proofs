import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S3
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S11
import Q1020K12L3S12
import Q1020K12L3S13
import Q1020K12L3S14
import Q1020K12L3S20
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S25
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S36
import Q1020K12L3S37
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S51
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S71
import Q1020K12L3S72
import Q1020K12L3S75
import Q1020K12L3S76
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S11Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_488 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_488 := by
  apply PetersenIndexedNode.close (bank := [s3_2336,a2179,a2180,a2181,a2182,s3_2994,s3_2414,s3_2413,s3_2412,s3_2411,a2183,a2184,a2185,a2186,a2187,a2188,s3_3158,s3_2995,s3_2444,a2189,a2190,s3_2996,a2191,a2192,a2193,s3_2999,s3_2486,s3_1806,a2194,s3_3003,a2195,a2196,a2197,s3_3008,s3_2543,a2198,a2199,s3_3013,a2200,s3_455,a2201,s3_3021,s3_21,s3_13,a2202,a825,a2203,a2204,a2205,a2206,s3_2997,a2207,a2208,a2209,a2210,a2211,s3_3000,a2212,s3_1860,a2213,s3_3004,a2214,s3_2774,a2215,a2216,a2217,s3_3009,s3_2867,a1136,a2218,s3_3014,a2219,s3_1053,s3_864,a2220,a1270,s3_3022,a2221,a2222,a2223,a2224,a2225,a2226,a2227,s3_2998,a2228,a2229,a2230,a2231,a2232,a2233,s3_3226,s3_3001,a2234,a2235,s3_1961,s3_1960,a2236,a2237,a2238,s3_3005,s3_2855,s3_2851,a2239,a2240,a2241,s3_3289,a2242,a2243,a2244,a2245,a2246,a2247,s3_3343,s3_3015,a1359,s3_1586,s3_1527,a2248,a807,s3_3027,a2249,a2250,a2251,s3_3002,a2252,s3_1981,a2253,s3_3006,a2254,a2255,a2256,a2257,s3_3029,s3_3010,a2258,a2259,a2260,s3_3016,a2261,s3_1191,a2262,s3_3023,a2263,a2264,a2265,s3_3007,a2266,a2267,a2268,s3_3011,a2269,a2270,a2271,s3_3017,a2272,a2273,a2274,s3_3024,a2275,a2276,a2277,s3_3012,a2278,a2279,s3_2084,s3_3018,a2280,a2281,a2282,s3_3025,a2283,a2284,a2285,s3_3019,a2286,s3_1365,a2287,s3_3026,a2288,a2289,a2290,s3_3028]) (PetersenIndexedNode.reasons 256 17 568 0x805ab111084044202805a210118504c202805b31111850484448059a1010840442028058a88885414a0008058210114100a0008059288894100a2228057a10105414840480569888854146202805610809c1804202805718889c1804222805590808541442028054a4040a080900080542101121009000805524041210090108053a1010a080840480529404121005000805210808a0805000805314040a08050108051908092100420280508e868a0803a0a80500a828e0c02a0a80510e868e0c02a1a804f8a828a0802a0a804ea303050408c04804e2101191808404804f230319180840c804da101050408404804c9202050404800804c1080890804800804d1202090804808804b9080850404202804a8a82890802a02804a2820050402a02804b0a82850402a0a8049a8200908048408048a6220504028208048141007060382080492622070602830804794100504028208046a10100c04840080462404109008400804721011090084048045a40400c0406028044930300c040602804410809898042028045130318980480c8043908080c04060280424020c0c04060280410a8284c4426028043402144c44062280408a8280c040602803f951100c040602803f141002c2416028040151102c240612803e941000c040602803d8b0900c040602803d0a0801c140e02803e0b0901c14060a803c8a0800c04060280252484a00ec9212803aa101200e88404803c2484a00ee92128023a101200e6840480381080a00de420280371202200da480880391080a00e2420280361202200d6480880348a82a00d02101801fa820200ce210180210a82a00d42a0a80332820200caa08080311c18200c2706080301410200be504080321c18200c67060802f1410200ba5040802d0a08200b22820802c1210200ae4840802e0a08200b62820802b1210200aa484080290180a00a20602802821202009e8480802a0180a00a60602802721202009a84808025248484c4892128024a10120090840480262484a009692128023a10104c4884048022908084c484202802212020c4c04808802310808c4c042028021920204c48480880208a82a00802a0a801fa82004c48262480210a8284c48280a801f28202007a280a801da4a084c482624801d141006c683624801e24a086c682634801c941004c482624801b0a8884c482a20801a8a08200682820801c0a88a006e282280198a0804c482820801881808c4c006028018212004c4826208019018084c4806028017a1200c4c062608017400b6005803018015c00a84c480301801421414060403028013a1011070483028014a1415070484058013210100604030280121242406040302801190808c2c04202801292424c2c048098011108080604030280102860406040302800f8a828424023028010a860442402120800f0a82806040302800e1450406040302800d9410026241302800e9450426240312800d1410006040302800c1250406040302800b8a08016140b02800c925041614030a800b0a08006040302800a21604060403028009818084a480602800aa16044a482124800901808060403028007c003a001b000c8005c0028060403028008c0040060403028004c0022000f00068001c000842402120800089890060403028002c00100604030280000989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2336 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1222 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2134 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2106 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3359 theta)
    · exact b3_2994 theta
    · exact b3_2414 theta
    · exact b3_2413 theta
    · exact b3_2412 theta
    · exact b3_2411 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_550 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_551 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2175 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2174 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2173 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2172 theta)
    · exact b3_3158 theta
    · exact b3_2995 theta
    · exact b3_2444 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2012 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2017 theta)
    · exact b3_2996 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2449 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1986 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2001 theta)
    · exact b3_2999 theta
    · exact b3_2486 theta
    · exact b3_1806 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1818 theta)
    · exact b3_3003 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2344 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1196 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2122 theta)
    · exact b3_3008 theta
    · exact b3_2543 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_463 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1880 theta)
    · exact b3_3013 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2551 theta)
    · exact b3_455 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1896 theta)
    · exact b3_3021 theta
    · exact b3_21 theta
    · exact b3_13 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_141 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_129 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_130 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2341 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2104 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1227 theta)
    · exact b3_2997 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2561 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1925 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1865 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_486 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3358 theta)
    · exact b3_3000 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2563 theta)
    · exact b3_1860 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_491 theta)
    · exact b3_3004 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2815 theta)
    · exact b3_2774 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_869 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1005 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_982 theta)
    · exact b3_3009 theta
    · exact b3_2867 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1396 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1414 theta)
    · exact b3_3014 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2779 theta)
    · exact b3_1053 theta
    · exact b3_864 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_987 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3360 theta)
    · exact b3_3022 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2438 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2437 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2169 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2168 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_537 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_538 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3163 theta)
    · exact b3_2998 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2619 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2618 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1971 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1970 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_420 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_421 theta)
    · exact b3_3226 theta
    · exact b3_3001 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2629 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2628 theta)
    · exact b3_1961 theta
    · exact b3_1960 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_390 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_391 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3231 theta)
    · exact b3_3005 theta
    · exact b3_2855 theta
    · exact b3_2851 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_981 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_600 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_601 theta)
    · exact b3_3289 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2914 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2913 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1461 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1460 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_589 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_590 theta)
    · exact b3_3343 theta
    · exact b3_3015 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2802 theta)
    · exact b3_1586 theta
    · exact b3_1527 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_981 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact b3_3027 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2491 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1811 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1816 theta)
    · exact b3_3002 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2451 theta)
    · exact b3_1981 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1999 theta)
    · exact b3_3006 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2553 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_460 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1946 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1891 theta)
    · exact b3_3029 theta
    · exact b3_3010 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2548 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_465 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1878 theta)
    · exact b3_3016 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2346 theta)
    · exact b3_1191 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2117 theta)
    · exact b3_3023 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2459 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1989 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1991 theta)
    · exact b3_3007 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2367 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1211 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2095 theta)
    · exact b3_3011 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2354 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1199 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2089 theta)
    · exact b3_3017 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2574 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_473 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1870 theta)
    · exact b3_3024 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2579 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_475 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1868 theta)
    · exact b3_3012 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2356 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1201 theta)
    · exact b3_2084 theta
    · exact b3_3018 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2372 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1209 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2093 theta)
    · exact b3_3025 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2786 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_934 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_961 theta)
    · exact b3_3019 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2875 theta)
    · exact b3_1365 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1371 theta)
    · exact b3_3026 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2788 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_958 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_937 theta)
    · exact b3_3028 theta
end Orbits1020Cost12
