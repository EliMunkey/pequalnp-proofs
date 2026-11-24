import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S11
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S24
import Q1020K12L3S26
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S33
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
import Q1020K12L3S52
import Q1020K12L3S54
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S63
import Q1020K12L3S64
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
import Q1020K12L3S81
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_522 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_522 := by
  apply PetersenIndexedNode.close (bank := [s3_2352,a3029,a3030,a3031,a3032,s3_3119,s3_2457,a3033,a3034,s3_3168,a3035,a3036,a3037,a3038,s3_2494,s3_1814,a3039,a3040,a3041,a3042,a3043,a3044,a3045,a3046,s3_2534,s3_2528,s3_2519,s3_2514,a3047,a3048,a3049,a3050,a3051,a3052,s3_3310,s3_3270,s3_2559,a3053,a3054,a3055,a3056,s3_471,a3057,a3058,a3059,a3060,a3061,a3062,a3063,a3064,a3065,a3066,a3067,s3_3197,a3068,s3_1876,a3069,a3070,a3071,s3_2823,s3_2782,a3072,a3073,a3074,a3075,s3_21,s3_18,a2700,s3_2883,a2871,a2827,s3_3273,a1322,s3_1124,s3_944,a3076,a1109,a3077,a3078,a3079,a3080,s3_3234,a3081,s3_1997,a3082,a3083,a3084,a3085,a3086,a3087,a3088,a3089,a3090,a3091,a3092,a3093,a3094,a3095,s3_3316,s3_3271,a3096,a3097,a3098,a3099,a3100,s3_1207,a3101,a3102,a3103,a3104,a3105,a3106,a3107,a3108,a3109,a3110,a3111,a3112,a3113,a3114,a3115,a3116,a3117,a3118,a3119,a3120,a3121,a3122,a3123,a3124,a3125,a3126,a3127,a3128,a3129,a3130,a3131,a3132,a3133,a3134,s3_2064,s3_2059,s3_3322,s3_3272,a3135,a3136,s3_2101,a3137,a3138,a3139,a3140,a3141,a2239,a3142,a3143,a2961,a2946,a3144,s3_3278,a1332,s3_1402,a3145,a3146,a2643,a3147,a2471,a3026,a2645,a2868,s3_3351,s3_3281,a1334,a1335,s3_1586,s3_1565,a3148,a3149,a807,a1339,a3150,a3151,a3152,s3_3290]) (PetersenIndexedNode.reasons 256 17 556 0x805ab111084044202805a210118504c202805b31111850484448059a10108404420280582484a015e9212805721012015a840480592484a016292128056210120156840480541080a014e4202805312022014a480880551080a01524202805212022014648088050a80805414a2028050210114504a2028051280814504a020804fa101054148404804e1888854146202804d9080a01344202804f1888a013a4222804c9080854144202801f40262007a210180214010454142101804b24040a0809000804aa101121009000804ba404121009010804a21010a080840480491404121005000804890808a0805000804994040a0805010804810809210042028046c0230a08050408045c0228e0c070608047c0238e0c070608044c0220a080504080430e868a0803a0a80428a828e0c02a0a80438e868e0c02a1a80420a828a0802a0a80412303050408c048040a1011918084048041a30319180840c80402101050408404803f1202050404800803e9080890804800803f9202090804808803e1080850404202803cc01e090804840803bc01d850402820803dc01e850402820803ac01d09080484080390a82890802a028038a8a0850402a0280398a82850402a0a803828a089080484080372622050402820803694100706038208037a622070602830803614100504028208035210100c0484008034a4041090084008035a1011090084048034240400c0406028033130300c040602803290809898042028033930318980480c8032108080c0406028030c018109008480802fc01780c0406028031c01880c040602802ec017109008480802cc01600c040602802b8a8284c442602802dc01684c440622802b0a8280c040602802a151100c0406028029941002c241602802a951102c2406128029141000c04060280280b0900c04060280278a0801c140e0280288b0901c14060a80270a0800c0406028025a48484c489212802521012009284048026a484a009892128024210104c4884048023108084c484202802292020c4c04808802390808c4c042028022120204c48480880204010e007e03018021401044c48030180200a82a007e2a0a801f400f44c482624801e400ee0074280a801c24a084c482624801b941006c683624801ca4a086c682634801b141004c48262480198a8884c482a2080190a08200622820801a8a88a0068282280180a0804c482820801701808c4c006028016a12004c4826208017818084c480602801621200c4c06260801521414060403028014a1011070483028015a1415070484058014210100604030280131242406040302801290808c2c04202801392424c2c04809801210808060403028010c0082003f001e800ec0070060403028011c008806040302800dc006a00330018800ac00500604030280098a82842402302800bc00584240212080090a82806040302800814504060403028007941002624130280089450426240312800714100060403028006125040604030280058a08016140b028006925041614030a80050a08006040302800421604060403028003818084a4806028004a16044a482124800301808060403028001c000842402120800089890060403028002c00100604030280000989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2352 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1230 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2142 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2129 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3392 theta)
    · exact b3_3119 theta
    · exact b3_2457 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2020 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2024 theta)
    · exact b3_3168 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2457 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2020 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2024 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3168 theta)
    · exact b3_2494 theta
    · exact b3_1814 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1828 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3237 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2352 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1230 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2142 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2129 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3392 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3119 theta)
    · exact b3_2534 theta
    · exact b3_2528 theta
    · exact b3_2519 theta
    · exact b3_2514 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_191 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_192 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2304 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2305 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2283 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2284 theta)
    · exact b3_3310 theta
    · exact b3_3270 theta
    · exact b3_2559 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_471 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1903 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3204 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2559 theta)
    · exact b3_471 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1903 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3204 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2375 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2115 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1234 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3130 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2572 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1947 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1899 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_494 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3370 theta)
    · exact b3_3197 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2586 theta)
    · exact b3_1876 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_498 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3208 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2823 theta)
    · exact b3_2823 theta
    · exact b3_2782 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1010 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_990 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1010 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_990 theta)
    · exact b3_21 theta
    · exact b3_18 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_981 theta)
    · exact b3_2883 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1402 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1419 theta)
    · exact b3_3273 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2800 theta)
    · exact b3_1124 theta
    · exact b3_944 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_998 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3402 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3278 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2497 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1826 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1826 theta)
    · exact b3_3234 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2465 theta)
    · exact b3_1997 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2010 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3173 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2572 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_494 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1947 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1899 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3370 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3197 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2673 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2671 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_173 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_176 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2211 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2209 theta)
    · exact b3_3316 theta
    · exact b3_3271 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2582 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_484 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1889 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3212 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2365 theta)
    · exact b3_1207 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2125 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3126 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2465 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1997 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2010 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3173 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2375 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1234 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2115 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3130 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2673 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2671 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_173 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_176 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2211 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2209 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3316 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3271 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2365 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1207 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2125 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3126 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2582 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_484 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1889 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3212 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2586 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_498 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1876 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3208 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2700 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2701 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_58 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_59 theta)
    · exact b3_2064 theta
    · exact b3_2059 theta
    · exact b3_3322 theta
    · exact b3_3272 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2379 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1220 theta)
    · exact b3_2101 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3134 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2379 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1220 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2101 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3134 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_981 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2800 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1124 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_944 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_998 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3402 theta)
    · exact b3_3278 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2883 theta)
    · exact b3_1402 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1419 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3273 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2942 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2936 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1586 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1565 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_129 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_134 theta)
    · exact b3_3351 theta
    · exact b3_3281 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2942 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2936 theta)
    · exact b3_1586 theta
    · exact b3_1565 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_129 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_134 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3281 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2803 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_973 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_973 theta)
    · exact b3_3290 theta
end Orbits1020Cost12
