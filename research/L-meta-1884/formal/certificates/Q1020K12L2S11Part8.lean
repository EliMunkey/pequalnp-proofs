import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S6
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S11
import Q1020K12L3S13
import Q1020K12L3S20
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S25
import Q1020K12L3S27
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S37
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
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
import Q1020K12L3S73
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
theorem b2_490 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_490 := by
  apply PetersenIndexedNode.close (bank := [s3_2338,a2402,a2403,a2404,a2405,s3_3070,s3_2428,s3_2427,a2406,a2407,a2408,a2409,s3_3160,s3_3071,s3_2446,a2410,a2411,s3_3072,a2412,a2413,a2414,s3_3075,s3_2488,s3_1808,a2415,s3_3079,a2416,a2417,a2418,s3_3084,s3_2545,a2419,a2420,s3_3089,a2421,s3_457,a2422,s3_3097,s3_21,s3_15,a2423,a2424,a2425,a2426,a2427,a2428,a2429,a2430,s3_3073,a2431,a2432,a2433,a2434,a2435,s3_3076,a2436,s3_1862,a2437,s3_3080,a2438,s3_2776,a2439,a2440,a2441,s3_3085,s3_2869,a2442,a2443,a2444,a2445,s3_3090,a2446,s3_1055,s3_866,a2447,a2448,s3_3098,a2449,a2450,a2451,a2452,a2453,a2454,a2455,s3_3074,a2456,a2457,a2458,a2459,a2460,a2461,s3_3228,s3_3077,a2462,a2463,s3_1965,s3_1964,a2464,a2465,a2466,s3_3081,a2467,a2468,a2239,a2469,a2470,s3_3289,s3_2887,a2471,a2472,a2473,s3_3351,s3_3095,a2474,a2475,s3_1146,s3_1145,a2476,a2477,a2478,s3_3099,a2479,a2480,a2481,s3_3078,a2482,s3_1983,a2483,s3_3082,a2484,a2485,a2486,s3_3086,a2487,a2488,a2489,s3_3091,a2490,s3_1193,a2491,s3_3100,a2492,a2493,a2494,s3_3083,a2495,a2496,a2497,s3_3087,a2498,a2499,a2500,s3_3092,a2501,a2502,a2503,s3_3101,a2504,a2505,a2506,s3_3088,a2507,a2508,s3_2086,s3_3093,a2509,a2510,a2511,s3_3102,a2512,a2513,a2514,s3_3094,a2515,s3_1367,a2516,s3_3103,a2517,a2518,a2519,s3_3104]) (PetersenIndexedNode.reasons 256 17 568 0x8059b1110840442028059210118504c202805a31111850484448058a1010840442028057a80805414a2028057210114504a2028058280814504a0208056a10105414840480559888854146101805510808c2826101805618888c2824222805490808541442028053a4040a080900080532101121009000805424041210090108052a1010a080840480519404121005000805110808a0805000805214040a080501080509080921004202804f8e868a0803a0a804f0a828e0c02a0a80500e868e0c02a1a804e8a828a0802a0a804da303050408c04804d2101191808404804e230319180840c804ca101050408404804b9202050404800804b1080890804800804c1202090804808804a908085040420280498a82890802a0280491850450402a02804a0a82850402a0a804898504908048408047a6220504028208047141007060382080482622070602830804694100504028208045a10100c04840080452404109008400804621011090084048044a40400c0406028043930300c040602804310809898042028044130318980480c8042908080c0406028041995140c04060280410a8284c4426028042195144c44062280408a8280c040602803f951100c040602803f141002c2416028040151102c240612803e941000c040602803d8b0900c040602803d0a0801c140e02803e0b0901c14060a803c8a0800c040602803b2484a00ea9212803a2101200e68404803c2484a00ee921280392101200e2840480221080a00dc420280369202200d8480880381080a00de420280209202200d6480880348a82a00d02101801e9850600ce210180200a82a00d42a0a80331850600ca6141803124a0a00c2928280301410200be5040803224a0a00c69282802f1410200ba5040802d0a08200b22820802c1210200ae4840802e0a08200b62820802b1210200aa484080290180a00a20602802821202009e8480802a0180a00a60602802721202009a84808025248484c4892128024a10120090840480262484a009692128023a10104c4884048022108084c4842028021920220084480880231080a008a42028020920204c484808801f8a82a007c2a0a801e985044c48262480200a8284c48280a801e185060076280a801ca4a084c482624801c141006c683624801d24a086c682634801b941004c482624801a0a8884c482a2080198a08200642820801b0a88a006a282280188a0804c48282080178180a005c06028016a12004c4826208018018084c480602801621202005684808015400a6005003018013c00984c480301801221414060403028011a1011070483028012a1415070484058011210100604030280101242406040302800f90808c2c04202801092424c2c04809800f1080806040302800e1850406040302800d8a82842402302800e9850442402120800d0a82806040302800c1450406040302800b9410026241302800c9450426240312800b1410006040302800a125040604030280098a08016140b02800a925041614030a80090a08006040302800821604060403028007818084a4806028008a16044a482124800701808060403028005c0028c2c061608004c0020060403028006c0030060403028003c0018c2c061608001c000842402120800089890060403028002c00100604030280000989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2338 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1224 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2135 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2108 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3365 theta)
    · exact b3_3070 theta
    · exact b3_2428 theta
    · exact b3_2427 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1158 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1159 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2179 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2178 theta)
    · exact b3_3160 theta
    · exact b3_3071 theta
    · exact b3_2446 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2014 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2015 theta)
    · exact b3_3072 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2447 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1984 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2003 theta)
    · exact b3_3075 theta
    · exact b3_2488 theta
    · exact b3_1808 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1820 theta)
    · exact b3_3079 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2342 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1194 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2120 theta)
    · exact b3_3084 theta
    · exact b3_2545 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_461 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1882 theta)
    · exact b3_3089 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2549 theta)
    · exact b3_457 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1894 theta)
    · exact b3_3097 theta
    · exact b3_21 theta
    · exact b3_15 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_270 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_264 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_258 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2403 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2339 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2107 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1237 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1225 theta)
    · exact b3_3073 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2564 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1923 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1863 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_488 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3364 theta)
    · exact b3_3076 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2565 theta)
    · exact b3_1862 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_489 theta)
    · exact b3_3080 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2814 theta)
    · exact b3_2776 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_867 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1006 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_984 theta)
    · exact b3_3085 theta
    · exact b3_2869 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1443 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1395 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1416 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3366 theta)
    · exact b3_3090 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2777 theta)
    · exact b3_1055 theta
    · exact b3_866 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_985 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3367 theta)
    · exact b3_3098 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2430 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2429 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2177 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2176 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1156 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1157 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3161 theta)
    · exact b3_3074 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2635 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2634 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1967 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1966 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_404 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_405 theta)
    · exact b3_3228 theta
    · exact b3_3077 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2637 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2636 theta)
    · exact b3_1965 theta
    · exact b3_1964 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_402 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_403 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3229 theta)
    · exact b3_3081 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2847 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2843 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_981 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_574 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_575 theta)
    · exact b3_3289 theta
    · exact b3_2887 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1586 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1561 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1413 theta)
    · exact b3_3351 theta
    · exact b3_3095 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2841 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2840 theta)
    · exact b3_1146 theta
    · exact b3_1145 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_585 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_586 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3305 theta)
    · exact b3_3099 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2489 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1809 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1819 theta)
    · exact b3_3078 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2448 theta)
    · exact b3_1983 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2002 theta)
    · exact b3_3082 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2550 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_458 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1893 theta)
    · exact b3_3086 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2546 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_462 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1881 theta)
    · exact b3_3091 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2343 theta)
    · exact b3_1193 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2119 theta)
    · exact b3_3100 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2460 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1987 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1988 theta)
    · exact b3_3083 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2369 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1213 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2092 theta)
    · exact b3_3087 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2357 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1197 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2087 theta)
    · exact b3_3092 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2576 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_476 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1867 theta)
    · exact b3_3101 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2577 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_477 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1866 theta)
    · exact b3_3088 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2358 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1198 theta)
    · exact b3_2086 theta
    · exact b3_3093 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2370 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1212 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2091 theta)
    · exact b3_3102 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2789 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_932 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_963 theta)
    · exact b3_3094 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2874 theta)
    · exact b3_1367 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1369 theta)
    · exact b3_3103 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2790 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_962 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_933 theta)
    · exact b3_3104 theta
end Orbits1020Cost12
