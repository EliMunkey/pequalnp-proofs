import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S3
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S11
import Q1020K12L3S14
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
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
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
theorem b2_515 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_515 := by
  apply PetersenIndexedNode.close (bank := [s3_2349,a2655,a2656,s3_3116,s3_2454,a2657,a2658,s3_3165,a2659,a2660,a2661,a2662,s3_2493,s3_1813,a2663,a2664,a2665,a2666,a2667,a2668,a2669,a2670,a2671,a2672,s3_2511,s3_2510,a2673,a2674,a2675,a2676,s3_3307,s3_3259,s3_2556,a2677,a2678,a2679,a2680,s3_468,a2681,a2682,a2683,a2684,a2685,a2686,a2687,a2688,a2689,s3_3194,a2690,s3_1873,a2691,a2692,s3_2817,s3_2781,a2693,a2694,a2695,a2696,a2697,s3_3258,s3_2942,s3_2931,a2698,a2699,a2700,s3_3289,s3_2880,a2701,a2702,s3_3261,a2703,s3_941,a2704,s3_3263,a2705,a2706,a2707,s3_3233,a2708,s3_1994,a2709,a2710,a2711,a2712,a2713,a2714,a2715,a2716,a2717,a2718,a2719,a2720,a2721,a2722,a2723,a2724,s3_3312,s3_3260,a2725,a2726,a2727,a2728,a2729,s3_1204,a2730,a2731,a2732,a2733,a2734,a2735,a2736,a2737,a2738,a2739,a2740,a2741,a2742,a2743,a2744,a2745,a2746,a2747,a2748,a2749,a2750,a2751,a2752,a2753,a2754,a2755,a2756,a2757,a2758,a2759,a2760,a2761,a2762,a2763,a2764,a2765,a2766,a2767,a2768,a2769,a2770,a2771,s3_2054,s3_2053,a2772,a2773,a2774,a2775,s3_2098,a2776,a2777,a2778,a2779,a2780,a2781,s3_21,s3_17,a2782,a2783,a2784,a2785,a2786,a2787,a2788,a2789,a2790,a2088,a2089,a1941,a1942,s3_1444,s3_1399,a2791,a2792,a2026,s3_3264,a2643,a2793,a2794,a2645,a2795,a2796,a2797,a2798,s3_1465,s3_1464,a2799,a2800,a2038,s3_3265,a2801,a2802,a2803,a2804]) (PetersenIndexedNode.reasons 256 17 568 0x8062311109010c4048061a1011911084048062b11119110844480612101090108404805fa8082017ca020805ea1012017884048060a80820180a020805da101201748404805c1888a016e4202805392022016c420280559888a01726222805a92022016848088058a80820160a0208057a1012015c84048059a80820164a0208056a10120158840480549888a01506222805392022014c480880559888a01544222805292022014848088051c028a0142210180504027e013c2101804e24040a0809000804da101121009000804ea404121009010804d21010a0808404804c1404121005000804b92020a0805000804c94040a0805010804b12021210048088049c0248a08050408048c0240e0c07060804ac0250e0c070608047c0238a08050408045c0228a08050408044c0220e0c070608046c0230e0c070608043c0218a080504080422303050408c048041a1011918084048042a30319180840c8041210105040840480401202050404800803f940409080480080409202090804808803f1404050405010803dc01e890804840803cc01e050402820803ec01f050402820803bc01d8908048408039c01c8908048408038c01c050402820803ac01d0504028208037c01b89080484080362622050402820803594100706038208036a622070602830803514100504028208034210100c0484008033a4041090084008034a1011090084048033240400c0406028032130300c040602803192021898048088032930318980480c8031120200c040602802fc01780c040602802ec01704c4426228030c01804c442622802dc01680c040602802bc01580c040602802ac01504c442622802cc01604c4426228029c01480c0406028028151100c0406028027941002c2416028028951102c2406128027141000c04060280260b0900c04060280258a0801c140e0280268b0901c14060a80250a0800c040602802424848060203018023a1011070283018024a4849070290128023210100602030180221888806020301802192020c4c04808802298888c4c0480a80211202006020301801cc010006020301801fc00f84c482624801dc01044c482624801ec00f006020301801cc00e006020301801bc00d84c482624801dc00e84c482624801ac00d006020301801924a0806020301801894100262213018019a4a08262203118018141000602030180170a8880602030180168a08016120b0180178a8881612030980160a08006020301801501808060206008014a12000c0806008015818080c08060280142120006020301801321414060403028012a1011070483028013a1415070484058012210100604030280111242406040302801092020c2c04808801192424c2c0480980101202006040302800ec007006040302800dc006842402120800fc007842402120800cc006006040302800ac0050060403028009c004842402120800bc0058424021208008c004006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800100c044240030080008181006040300800180c040604030180000181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2349 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1205 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2124 theta)
    · exact b3_3116 theta
    · exact b3_2454 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1995 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2009 theta)
    · exact b3_3165 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2455 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2019 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2019 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3166 theta)
    · exact b3_2493 theta
    · exact b3_1813 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1825 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3233 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2404 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2350 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1238 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1229 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2138 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2114 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3387 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3117 theta)
    · exact b3_2511 theta
    · exact b3_2510 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_372 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_373 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2200 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2199 theta)
    · exact b3_3307 theta
    · exact b3_3259 theta
    · exact b3_2556 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_469 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1898 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3194 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2557 theta)
    · exact b3_468 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1888 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3203 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2374 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2098 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1219 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3129 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2556 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1898 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_469 theta)
    · exact b3_3194 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2581 theta)
    · exact b3_1873 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_483 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3207 theta)
    · exact b3_2817 theta
    · exact b3_2781 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1009 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_989 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1105 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_942 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3384 theta)
    · exact b3_3258 theta
    · exact b3_2942 theta
    · exact b3_2931 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_129 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_131 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_981 theta)
    · exact b3_3289 theta
    · exact b3_2880 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1400 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1400 theta)
    · exact b3_3261 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2799 theta)
    · exact b3_941 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_972 theta)
    · exact b3_3263 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2493 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1825 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1813 theta)
    · exact b3_3233 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2464 theta)
    · exact b3_1994 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1994 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3172 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2591 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2571 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_501 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_493 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1931 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1874 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3369 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3195 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2664 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2663 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_369 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_370 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2054 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2053 theta)
    · exact b3_3312 theta
    · exact b3_3260 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2581 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_483 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1873 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3207 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2364 theta)
    · exact b3_1204 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2099 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3125 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2454 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1995 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2009 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3165 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2404 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2350 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1238 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1229 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2138 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2114 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3387 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3117 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2511 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2510 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_372 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_373 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2200 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2199 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3307 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3259 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2349 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1205 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2124 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3116 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2557 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_468 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1888 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3203 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2591 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2571 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_501 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_493 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1931 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1874 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3369 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3195 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2664 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2663 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_369 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_370 theta)
    · exact b3_2054 theta
    · exact b3_2053 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3312 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3260 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2374 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1219 theta)
    · exact b3_2098 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3129 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2364 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1204 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2099 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3125 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_22 theta)
    · exact b3_21 theta
    · exact b3_17 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_605 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_600 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_602 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2817 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2781 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1105 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_942 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1009 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_989 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3384 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3258 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2902 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2881 theta)
    · exact b3_1444 theta
    · exact b3_1399 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1430 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1418 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3389 theta)
    · exact b3_3264 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2942 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2931 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_981 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_129 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_131 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3289 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2929 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2928 theta)
    · exact b3_1465 theta
    · exact b3_1464 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_378 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_379 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3348 theta)
    · exact b3_3265 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2799 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_941 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_972 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3263 theta)
end Orbits1020Cost12
