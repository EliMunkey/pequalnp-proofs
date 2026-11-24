import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S3
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S11
import Q1020K12L3S13
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S24
import Q1020K12L3S26
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S51
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S63
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S74
import Q1020K12L3S75
import Q1020K12L3S76
import Q1020K12L3S77
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_514 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_514 := by
  apply PetersenIndexedNode.close (bank := [s3_2348,a2520,a2521,a2522,a2523,s3_3115,s3_2453,a2524,a2525,s3_3164,a2526,a2527,a2528,a2529,s3_2492,s3_1812,a2530,a2531,a2532,a2533,a2534,a2535,s3_2509,s3_2508,a2536,a2537,a2538,a2539,s3_3306,s3_3246,s3_2555,a2540,a2541,a2542,a2543,s3_467,a2544,a2545,a2546,a2547,a2548,a2549,a2550,a2551,a2552,a2553,a2554,s3_3193,a2555,s3_1930,s3_1872,a2556,a2557,a2558,a2559,s3_2780,a2560,a2561,a2562,s3_3245,s3_21,s3_16,a2563,a2469,a2564,a2565,s3_2878,a2566,a2567,a2568,s3_3250,a2569,s3_1100,s3_940,a2570,a2571,s3_3253,a2572,a2573,a2574,s3_3232,a2575,s3_1993,a2576,a2577,a2578,a2579,a2580,a2581,a2582,a2583,a2584,a2585,a2586,a2587,s3_3311,s3_3247,a2588,a2589,a2590,a2591,a2592,s3_1203,a2593,a2594,a2595,a2596,a2597,a2598,a2599,a2600,a2601,a2602,a2603,a2604,a2605,a2606,a2607,a2608,a2609,s3_3248,a2610,a2611,a2612,a2613,a2614,a2615,a2616,a2617,a2618,a2619,a2620,a2621,a2622,a2623,a2624,a2625,s3_2052,s3_2051,s3_3319,s3_3249,a2626,a2627,s3_2097,a2628,a2629,a2630,a2631,a2632,a2633,a2634,a2424,a2635,a2239,s3_3289,a2636,a2637,a2638,a2639,a2640,s3_3251,a2641,s3_1398,a2642,s3_3254,a2643,a2644,a2356,a2645,a2646,s3_3333,a2647,a2648,s3_1463,s3_1462,a2649,a2650,a2651,s3_3255,a2652,a2653,a2654,s3_3256]) (PetersenIndexedNode.reasons 256 17 568 0x805ab111084044202805a210118504c202805b31111850484448059a10108404420280582484a015e9212805721012015a840480592484a016292128056210120156840480549080a01504202802192022014e480880231080a01544202805312022014a48088051a80804202a0008051210114100a0008052280814100a0208050a101042022101804f1888842022101804e9080a0138420280501888a013e4222804d9080842022101801c4026442022101804c4025c54142a0a801dc026854142a0a804b40254420221018049a4040a080900080492101121009000804a24041210090108048a1010a080840480479404121005000804710808a0805000804814040a080501080469080921004202804540224a080504080444021ce0c0706080464022ce0c07060804340214a080504080418c444a0803101804108404e0c0210180420c444e0c02111804088404a0802101803fa303050408c04803f21011918084048040230319180840c803ea101050408404803d9202050404800803d1080890804800803e1202090804808803c9080850404202803b401d450402820803a401cc54442a22803c401dc54442a228039401c45040282080378a020908028008037084045040280080380a02050402808803688404908021018035a6220504028208035141007060382080362622070602830803494100504028208033a10100c04840080332404109008400803421011090084048032a40400c0406028031930300c040602803110809898042028032130318980480c8030908080c040602802f4017509008480802e4016c0c04060280304017c0c040602802d4016509008480802b894140c042501802b084044c442101802c094144c442105802a884040c0421018029951100c0406028029141002c241602802a151102c2406128028941000c04060280278b0900c04060280270a0801c140e0280280b0901c14060a80268a0800c040602802524848c4c092128024a10120090840480262484a009692128023a1010c4c0840480229080a00884202802192020c4c04808802310808c4c04202802112022008248088020400fe007c0301801ec00f0c4c00301801d0a82a00722a0a801c08404c4c02101801d8a828c4c02a0a801b88406006c21018019a4a08c4c0626080191410200625040801aa4a0a00689282801814100c4c0504080168a888c4c02a2280160a0820056282080178a88a005c2a2280150a080c4c02820801401808c4c006028013a1200ccc86660801481808ccc80602801321200c4c06260801221414060403028011a1011070483028012a1415070484058011210100604030280101242406040302800f90808c2c04202801092424c2c04809800f1080806040302800dc006842402120800cc006006040302800ec007006040302800bc005842402120800a084040604210080098a02042402100800a884044240210180090a02006040302800814504060403028007941002624130280089450426240312800714100060403028006125040604030280058a08016140b028006925041614030a80050a08006040302800421604060403028003818084a4806028004a16044a482124800301808060403028001c000842402120800098980060403028002c00100604030280001898042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2348 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1228 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2136 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2111 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3381 theta)
    · exact b3_3115 theta
    · exact b3_2453 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2018 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2021 theta)
    · exact b3_3164 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2456 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2005 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2006 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3167 theta)
    · exact b3_2492 theta
    · exact b3_1812 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1823 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3235 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2351 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1215 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2126 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3118 theta)
    · exact b3_2509 theta
    · exact b3_2508 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_283 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_284 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2186 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2185 theta)
    · exact b3_3306 theta
    · exact b3_3246 theta
    · exact b3_2555 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_470 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1885 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3198 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2558 theta)
    · exact b3_467 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1900 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3202 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2360 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2109 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1231 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3121 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2566 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1937 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1884 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_492 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3368 theta)
    · exact b3_3193 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2568 theta)
    · exact b3_1930 theta
    · exact b3_1872 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_495 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3375 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3199 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2819 theta)
    · exact b3_2780 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_965 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1008 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_988 theta)
    · exact b3_3245 theta
    · exact b3_21 theta
    · exact b3_16 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_581 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_574 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_577 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2897 theta)
    · exact b3_2878 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1401 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1429 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1417 theta)
    · exact b3_3250 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2794 theta)
    · exact b3_1100 theta
    · exact b3_940 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_991 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3382 theta)
    · exact b3_3253 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2495 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1822 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1821 theta)
    · exact b3_3232 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2463 theta)
    · exact b3_1993 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2004 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3171 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2570 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_479 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1897 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3196 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2645 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2644 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_279 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_280 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2182 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2181 theta)
    · exact b3_3311 theta
    · exact b3_3247 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2567 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_482 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1883 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3200 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2363 theta)
    · exact b3_1203 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2123 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3124 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2461 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1996 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2008 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3169 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2373 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1216 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2113 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3128 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2643 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2642 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_281 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_282 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2184 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2183 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3313 theta)
    · exact b3_3248 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2359 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1206 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2110 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3120 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2580 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_478 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1887 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3209 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2583 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_480 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1875 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3206 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2647 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2646 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_225 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_226 theta)
    · exact b3_2052 theta
    · exact b3_2051 theta
    · exact b3_3319 theta
    · exact b3_3249 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2361 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1218 theta)
    · exact b3_2097 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3122 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2376 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1214 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2100 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3131 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2975 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2970 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_264 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_259 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_981 theta)
    · exact b3_3289 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2793 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1106 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_943 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_966 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3323 theta)
    · exact b3_3251 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2882 theta)
    · exact b3_1398 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1406 theta)
    · exact b3_3254 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2942 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2933 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1413 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_129 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_126 theta)
    · exact b3_3333 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2927 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2926 theta)
    · exact b3_1463 theta
    · exact b3_1462 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_277 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_278 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3347 theta)
    · exact b3_3255 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2795 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_964 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_971 theta)
    · exact b3_3256 theta
end Orbits1020Cost12
