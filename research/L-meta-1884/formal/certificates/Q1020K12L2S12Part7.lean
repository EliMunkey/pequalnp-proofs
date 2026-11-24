import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S4
import Q1020K12L3S23
import Q1020K12L3S26
import Q1020K12L3S37
import Q1020K12L3S46
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S52
import Q1020K12L3S54
import Q1020K12L3S60
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S67
import Q1020K12L3S70
import Q1020K12L3S77
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S81
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_523 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_523 := by
  apply PetersenIndexedNode.close (bank := [a3153,a3154,a3155,a3156,s3_2535,s3_2529,s3_2520,a3157,a3158,a3159,a3160,a3161,s3_2697,s3_55,a3162,s3_3291,a3163,a3164,a1872,s3_2827,a3165,a3166,a764,a1852,s3_1132,a3167,a3168,a3169,s3_3301,a3170,s3_122,a3171,s3_3292,a3172,a3173,a3174,a3175,a3176,a3177,a3178,a3179,a3180,s3_170,a3181,s3_3293,a3182,a3183,a3184,a3185,a3186,s3_3303,a3187,a3188,a3189,a3190,a3191,a3192,s3_2065,a3193,s3_2102,a3194,a3195,s3_3304,a3196,a3197,a3198,s3_188,s3_2287,s3_2288,s3_2280,s3_3294,a1837,a3199,a3200,a3201,a3202,a2963,a3203,a3204,a3205,a2967,a3206,a3207,a3208,a3209,a3210,s3_1594,a3211,a3212,s3_3267,a3213,s3_3266,s3_197,s3_198,s3_196,a3214,a3215,a3216,s3_3357,a3217,s3_3295,a3218,a3219,a3220,a3221,s3_18,a3152,a3151]) (PetersenIndexedNode.reasons 256 17 510 0x200d700674202401a5888884048035401a0840500696141108098889006862224019d8504c2828033401950889006180304017e00bd005d802e4019200c70062802dc016a00b2e060802bb81818889005662223818200b0e0606222401558888c2828029b0a0991110052644430a0a00a8c2826444401459111004f15050a82a009ca2825141401414504a28280268a8285414e06015050a8298888a2826222381814504e06062220a8285415004915050a829850500486141401320097004a61410a82854150047800a08406002c2a0a1080c011600890043802114100a081004628201410200830040801fc00f4a0805040622224201a081003e484024201888850402820400ed21009080614114100a081003c282014101850490804840400e4a0805040801c1c180e0c1003a38301c182006e504028200e868a0803a0a15051c18054143a1a38300a868541450401505400d450402820801a1210090810036242012102006628201410400c4504028206222323019081003264601230188882820141032220504028206141121009080c888242012101850428201410400bc9080484080170a0805041003014100a082005a484024200a82890802a0251410a08054042a0a14100a829450448402420262205040282028200e0c0704098881c180a0c0a08028201410400ac0c0406028015212010901002c424021202005206020301311100c0406027030212018880c444424031111c0c0060203014009c0c0406026141313018901002862602130185040602030140095090084808012018080c05002603010180a004684804240400840c0406021505098884c050022131101888541406020301151100c0406022820058482c0454440b0901848a080060203010b0900c0406021410038281c042c240705018285040060203014007c4c482624800f18980c4c10020313018982003a26241312400644c4826246222400618889001c800dc006988882624131230a084c482624644418980c4c0c2823130189819110262413124005e002a0301800b0989006022a0a800a8a82a0028262413124004e0024280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080080a0805445001114110a0804c4828200301189800c0484801312098800c042624030121200c4c06260800700c080605000d30b018582001e616030b0400300604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a080604030280054002600110007018100c0a0016030201814001a000b0004800100c0806042a0a109008c0a0006212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030280000848042402624018100c0a0002030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b3_2102 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3304 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2102 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3304 theta)
    · exact b3_2535 theta
    · exact b3_2529 theta
    · exact b3_2520 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_188 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2287 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2288 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2280 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3294 theta)
    · exact b3_2697 theta
    · exact b3_55 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2065 theta)
    · exact b3_3291 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1945 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3303 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2827 theta)
    · exact b3_2827 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_974 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_974 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_18 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_973 theta)
    · exact b3_1132 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1132 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3408 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3301 theta)
    · exact b3_3301 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2943 theta)
    · exact b3_122 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1594 theta)
    · exact b3_3292 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1945 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3303 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2674 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_170 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2212 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3293 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1945 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3303 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2674 theta)
    · exact b3_170 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2212 theta)
    · exact b3_3293 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2674 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_170 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2212 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3293 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1945 theta)
    · exact b3_3303 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2674 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_170 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2212 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3293 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2697 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_55 theta)
    · exact b3_2065 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3291 theta)
    · exact b3_2102 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3304 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2102 theta)
    · exact b3_3304 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2535 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2529 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2520 theta)
    · exact b3_188 theta
    · exact b3_2287 theta
    · exact b3_2288 theta
    · exact b3_2280 theta
    · exact b3_3294 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_973 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1132 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1132 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3408 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3301 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3301 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2943 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_122 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1594 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3292 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2943 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1594 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_122 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3292 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2943 theta)
    · exact b3_1594 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_122 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3292 theta)
    · exact b3_3267 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3266 theta)
    · exact b3_3266 theta
    · exact b3_197 theta
    · exact b3_198 theta
    · exact b3_196 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_197 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_196 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_198 theta)
    · exact b3_3357 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3295 theta)
    · exact b3_3295 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2827 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2827 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_974 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_974 theta)
    · exact b3_18 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_973 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_973 theta)
end Orbits1020Cost12
