import Q1020K12L2S12Local
import Q1020K12L3S3
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S11
import Q1020K12L3S12
import Q1020K12L3S24
import Q1020K12L3S26
import Q1020K12L3S29
import Q1020K12L3S34
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S48
import Q1020K12L3S50
import Q1020K12L3S51
import Q1020K12L3S52
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S63
import Q1020K12L3S66
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
theorem b2_535 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_535 := by
  apply PetersenIndexedNode.close (bank := [s3_2382,a3595,a3596,s3_3137,s3_2470,a3597,a3598,s3_3178,a3599,a3600,a3601,a3602,s3_2499,s3_1830,a3603,a3604,a3605,a3606,a3607,a3608,s3_2589,a3609,a3610,a3611,a3612,s3_371,a3613,s3_3386,a3614,a3615,a3616,a3617,a3618,a3619,a3620,s3_3215,a3621,s3_1906,a3622,a3623,s3_2810,a3624,a3625,s3_3299,s3_2893,a3626,a3627,s3_3340,a3628,s3_143,a3629,s3_3384,a3630,a3631,a3632,s3_3239,a3633,s3_2027,a3634,a3635,a3636,a3637,a3638,a3639,a3640,a3641,a3642,a3643,a3644,s3_374,a3645,s3_3388,a3646,a3647,a3648,a3649,a3650,a3651,a3652,a3653,a3654,a3655,a3656,a3657,a3658,a3659,a3660,a3661,a3662,a3663,a3664,a3665,a3666,a3667,s3_2132,a3668,a3669,a3670,a3671,a3672,a3673,a3674,a3675,a3676,a3677,s3_380,a3678,s3_3390,a3679,a3680,a3681,a3682]) (PetersenIndexedNode.reasons 256 17 448 0x803731110901042028036a1010850442028037b111085048444803621010901084048035280804202a0008034a10114100a0008035a80814100a0208034210104202210180331c0c042022101803292020c282610180339c0c0c282503080321202042022101803124040a08090008030a1011210090008031a404121009010803021010a0808404802f1404121005000802e92020a0805000802f94040a0805010802e1202121004808802d0c444a0803101802c88404e0c02101802d8c444e0c02111802c08404a0802101802b2303050408c04802aa101191808404802ba30319180840c802a21010504084048029120205040480080289404090804800802992020908048088028140405040501080270a020908028008026884045040280080278a020504028088026084049080210180252622050402820802494100706038208025a622070602830802414100504028208023210100c0484008022a4041090084008023a1011090084048022240400c0406028021130300c040602802092021898048088021930318980480c8020120200c040602801f094140c042501801e884044c442101801f894144c442105801e084040c042101801d151100c040602801c941002c241602801d951102c240612801c141000c040602801b0b0900c040602801a8a0801c140e02801b8b0901c14060a801a0a0800c040602801924848060203018018a1011070283018019a48490702901280182101006020301801710a080602030180169202085804808801790a088580480a8016120200602030180150a828060203018014884044c48210180158a8284c48280a80140840406020301801324a0806020301801294100262213018013a4a08262203118012141000602030180110a8880602030180108a08016120b0180118a8881612030980100a08006020301800f0180806020600800ea12000c080600800f818080c080602800e2120006020301800d2141406040302800ca101107048302800da141507048405800c2101006040302800b1242406040302800a92020c2c04808800b92424c2c04809800a12020060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800100c044240030080008181006040300800180c040604030180000181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2382 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1240 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2146 theta)
    · exact b3_3137 theta
    · exact b3_2470 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2029 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2038 theta)
    · exact b3_3178 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2472 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2031 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2031 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3180 theta)
    · exact b3_2499 theta
    · exact b3_1830 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1832 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3239 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2384 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1242 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2159 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3139 theta)
    · exact b3_2589 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_503 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1910 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3215 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2665 theta)
    · exact b3_371 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2055 theta)
    · exact b3_3386 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2386 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2132 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1255 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3141 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2589 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1910 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_503 theta)
    · exact b3_3215 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2593 theta)
    · exact b3_1906 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_522 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3219 theta)
    · exact b3_2810 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1027 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1023 theta)
    · exact b3_3299 theta
    · exact b3_2893 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1441 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1441 theta)
    · exact b3_3340 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2951 theta)
    · exact b3_143 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1105 theta)
    · exact b3_3384 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2499 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1832 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1830 theta)
    · exact b3_3239 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2479 theta)
    · exact b3_2027 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2027 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3187 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2610 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_505 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1908 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3217 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2593 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_522 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1906 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3219 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2512 theta)
    · exact b3_374 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2201 theta)
    · exact b3_3388 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2470 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2029 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2038 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3178 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2384 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1242 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2159 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3139 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2382 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1240 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2146 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3137 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2665 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_371 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2055 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3386 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2610 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_505 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1908 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3217 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2386 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1255 theta)
    · exact b3_2132 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3141 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2512 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_374 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2201 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3388 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2810 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1023 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1027 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3299 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2930 theta)
    · exact b3_380 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1466 theta)
    · exact b3_3390 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2951 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_143 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1105 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3384 theta)
end Orbits1020Cost12
