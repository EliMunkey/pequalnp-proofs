import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S11
import Q1020K12L3S23
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S39
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S50
import Q1020K12L3S52
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S61
import Q1020K12L3S63
import Q1020K12L3S66
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S74
import Q1020K12L3S75
import Q1020K12L3S76
import Q1020K12L3S77
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_529 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_529 := by
  apply PetersenIndexedNode.close (bank := [s3_2362,a3281,a3282,s3_3123,s3_2462,a3283,a3284,s3_3170,a3285,a3286,a3287,a3288,s3_2496,s3_1824,a3289,a3290,a3291,a3292,a3293,a3294,s3_2569,a3295,a3296,a3297,a3298,a3299,s3_2655,s3_2652,a3300,a3301,a3302,a3303,s3_3345,s3_3328,a3304,s3_481,a3305,a3306,a3307,a3308,a3309,a3310,a3311,a3312,a3313,a3314,a3315,s3_3201,a3316,s3_1940,s3_1886,a3317,a3318,a3319,s3_2796,a2850,a2823,s3_3273,a3320,s3_2900,s3_2885,a3321,a3322,a3323,a3324,s3_21,s3_19,a2473,a1405,s3_967,a3325,a3326,a3327,a3328,a3329,s3_3236,a3330,s3_2007,a3331,a3332,a3333,a3334,a3335,a3336,a3337,a3338,a3339,a3340,a3341,a3342,a3343,a3344,a3345,a3346,a3347,a3348,a3349,a3350,a3351,s3_1217,a3352,a3353,a3354,a3355,a3356,a3357,a3358,a3359,a3360,a3361,a3362,a3363,a3364,a3365,a3366,a3367,a3368,a3369,a3370,a3371,a3372,a3373,a3374,a3375,a3376,a3377,a3378,a3379,a3380,a3381,a3382,a3383,s3_2112,a3384,a3385,a3386,a3387,a3388,s3_2194,s3_2191,a3389,a3390,a3391,a3392,a3393,a3394,a3395,a3396,a3397,a3398,a2633,a3399,a2424,a2867,a3400,a3274,s3_3351,s3_3330,a1235,s3_1407,a3401,s3_3334,a2356,a1418,a1417,a3402,a3403,a1420,a1421,s3_1673,s3_1667,a3404,a3405,a780,a1422]) (PetersenIndexedNode.reasons 256 17 556 0x80562484a015692128055210120152840480572484a015a9212805421012014e84048052b1110840442028052210118504c2028053311118504c4448051a101084044202801f4028a007a4808802140104840442028050280804202a000804fa10114100a0008050a80814100a020804f2101042022101804dc026842022101804cc026054142a0a804ec027054142a0a804bc025842022101804a1888842022101804990808c2824202804a98888c282422280491080842022101804824040a08090008047a1011210090008048a404121009010804721010a08084048045c0229210090808044c0220a08050408046c0230a08050408043c02192100908080421484921005202804190808a0804202804294848a08042128041108092100420280400c444a0803101803f88404e0c0210180408c444e0c02111803f08404a0802101803e2303050408c04803da101191808404803ea30319180840c803d2101050408404803bc01d850402820803ac01d054442a22803cc01e054442a228039c01c85040282080381282850404a02803790808908042028038928289080420a8037108085040420280360a020908028008035884045040280080368a020504028088035084049080210180342622050402820803394100706038208034a622070602830803314100504028208032210100c0484008031a4041090084008032a1011090084048031240400c040602802fc017909008480802ec01700c0406028030c01800c040602802dc016909008480802bc01580c040602802a9080989804202802cc01618980c4c0802a108080c0406028029094140c0425018028884044c4421018029894144c4421058028084040c0421018027151100c0406028026941002c2416028027951102c2406128026141000c04060280250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c040602802324848848092128022a1011858084048023a4849858092128022210108480840480204010e007e03018021401048480030180201080a007e4202801f400f484804240801e400ee0074480a801c0a82884802a0a801b88404c4c02101801c8a828c4c02a0a801b08404848021018019a4a088480424080191410200625040801aa4a0a006892828018141008480424080168a88884802a2280160a0820056282080178a88a005c2a2280150a08084802820801401808848006028013a12008c8846408014818088c88060280132120084804240801221414060403028011a1011070483028012a14150704840580112101006040302800fc007842402120800ec0070060403028010c008006040302800dc006842402120800bc005806040302800a90808c2c04202800cc0060c2c06160800a10808060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800110d044240212080009090006040302800190d040604030280001090042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2362 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1232 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2112 theta)
    · exact b3_3123 theta
    · exact b3_2462 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2022 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2022 theta)
    · exact b3_3170 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2467 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2007 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2007 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3175 theta)
    · exact b3_2496 theta
    · exact b3_1824 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1824 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3236 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2377 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1217 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2127 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3132 theta)
    · exact b3_2569 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_496 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1940 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1886 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3376 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3201 theta)
    · exact b3_2655 theta
    · exact b3_2652 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_219 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_221 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2194 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2191 theta)
    · exact b3_3345 theta
    · exact b3_3328 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2584 theta)
    · exact b3_481 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1901 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3210 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2362 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2112 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1232 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3123 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2569 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1940 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1886 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_496 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3376 theta)
    · exact b3_3201 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2569 theta)
    · exact b3_1940 theta
    · exact b3_1886 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_496 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3376 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3201 theta)
    · exact b3_2796 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_967 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_992 theta)
    · exact b3_3273 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2900 theta)
    · exact b3_2900 theta
    · exact b3_2885 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1434 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1424 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1434 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1424 theta)
    · exact b3_21 theta
    · exact b3_19 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1413 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2796 theta)
    · exact b3_967 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_992 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3273 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2496 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1824 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1824 theta)
    · exact b3_3236 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2467 theta)
    · exact b3_2007 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2007 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3175 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2584 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_481 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1901 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3210 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2569 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_496 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1940 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1886 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3376 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3201 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2655 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2652 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_219 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_221 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2194 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2191 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3345 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3328 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2377 theta)
    · exact b3_1217 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2127 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3132 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2462 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2022 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2022 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3170 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2377 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1217 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2127 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3132 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2362 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1232 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2112 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3123 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2655 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2652 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_219 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_221 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2194 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2191 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3345 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3328 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2584 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_481 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1901 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3210 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2584 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_481 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1901 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3210 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2362 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1232 theta)
    · exact b3_2112 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3123 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2655 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2652 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_219 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_221 theta)
    · exact b3_2194 theta
    · exact b3_2191 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3345 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3328 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2377 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1217 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2127 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3132 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2796 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_992 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_967 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3273 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2975 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2976 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_264 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_265 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1673 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1667 theta)
    · exact b3_3351 theta
    · exact b3_3330 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2888 theta)
    · exact b3_1407 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1407 theta)
    · exact b3_3334 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1413 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2796 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_967 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_992 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3273 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2975 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2976 theta)
    · exact b3_1673 theta
    · exact b3_1667 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_264 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_265 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3351 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3330 theta)
end Orbits1020Cost12
