import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S12
import Q1020K12L3S24
import Q1020K12L3S26
import Q1020K12L3S27
import Q1020K12L3S29
import Q1020K12L3S34
import Q1020K12L3S38
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S51
import Q1020K12L3S52
import Q1020K12L3S54
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S66
import Q1020K12L3S68
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
theorem b2_537 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_537 := by
  apply PetersenIndexedNode.close (bank := [s3_2383,a3683,a3684,s3_3138,s3_2471,a3685,a3686,s3_3179,a3687,a3688,a3689,a3690,s3_2500,s3_1831,a3691,a3692,a3693,a3694,a3695,a3696,s3_2590,a3697,a3698,a3699,a3700,a3701,a3702,s3_3391,s3_2703,s3_61,a3703,a3704,s3_3404,a3705,a3706,a3707,a3708,a3709,a3710,a3711,a3712,a3713,a3714,s3_3216,a3715,s3_1954,s3_1907,a3716,a3717,a3718,s3_2811,a3719,a3720,a3721,a3168,s3_3301,s3_2895,a3722,a3723,s3_3342,s3_23,a3724,a3725,a3726,a3727,a3728,a3729,s3_144,s3_145,a3730,a3731,s3_3403,a3732,a3733,a3734,s3_3240,a3735,s3_2028,a3736,a3737,a3738,a3739,a3740,a3741,a3742,a3743,a3744,a3745,s3_3406,a3746,a3747,a3748,a3749,a3750,a3751,s3_3397,a3752,s3_179,a3753,a3754,s3_3405,a3755,a3756,a3757,a3758,a3759,a3760,a3761,a3762,a3763,a3764,a3765,a3766,a3767,a3768,a3769,a3770,a3771,a3772,s3_3398,a3773,a3774,a3775,a3776,a3777,a3778,a3779,a3780,a3781,a3782,s3_2145,s3_2133,s3_3407,a3783,a3784,a3785,a3786,a3787,a3788,s3_3399,a3789,a3790,s3_194,s3_2312,s3_2286,a3791,a3792,a3793,a3794,a3795,s3_3408,a3796,a3797,a3798,a3799,s3_3401,a3800,a3801,a3802,a3803,a3804,a3805,a3806,a3807,a3808,a3809,a3810,a3811,a3812,a3813,s3_3383,a3682,s3_3384,s3_3385]) (PetersenIndexedNode.reasons 256 17 560 0x80522484a0146840480224010d888884048023a4849888892128056c02b2015700aa8054c02a2014e4202801e2484885044202805331112014ac44480524028c850442828023b11108504844480514028601408444804f2888842022101804ea4848c282a202804fa8888c282a222804e2484842022101804d3818042022101804cb111054142a0a804db818054142a0a804c3111042022101804ac025042022101804990a08c2826141804bc0258c2826141804910a084202210180482484a011e9202804728888a08092028048a4848a08092128046a888a0118a2228044c0220a08050408043b11112100d0408045c022921009080804331110a08050408041c020921009080804090a08a08050408042c0210a0805040804010a0921009080803f0c444a0803101803e88404e0c02101803f8c444e0c02111803e08404a0802101803d2686850409a12803ca484890809212803da68689080921a803c2484850409212803ac01d0504028208039b111054442a22803bc01d854442a228039311105040282080383222050402820803790a08908048408038b222090804840803710a085040282080360a020908028008035884045040280080368a020504028088035084049080210180342622050402820803394100706038208034a622070602830803314100504028208031c01880c0406028030a4849090086028032c0191090084808030248480c040602802f3111200bac440802e381800c040602802fb11100c040602802db818200b4e060802bc01580c040602802a90a098980c480802cc0161898084c0802a10a080c0406028029094140c0425018028884044c4421018029894144c4421058028084040c0421018027151100c0406028026941002c2416028027951102c2406128026141000c04060280250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c04060280232484a008a921280224010d070283818023a48490702901280214010600809012801fc00fa007a0301801e3111107020301801d10a0907024280801cb222085804280801d90a0885804282801c3222107028381801a8a82907022a0a801a0840600662101801b8a82a006c2a0a801908405070221018017a4a0907029280801714102005a50408018a4a0a006090828016141010702504080150a88907022a2280148a0811712282080158a88917122a2280140a08107022820801281809070206028012212020046848080138180a004c060280112120107028480800fc007806040302800ea4848c2c083028010c0080c2c06160800e2484806040302800d3151442402120800cb111006040302800db151406040302800c3111042402120800b3262406040302800a90a08c2c06160800bb2624c2c06160800a10a08060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800120e0442402120800090b00060403028001a0e0406040302800010b0042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2383 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1241 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2147 theta)
    · exact b3_3138 theta
    · exact b3_2471 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2030 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2039 theta)
    · exact b3_3179 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2473 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2032 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2032 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3181 theta)
    · exact b3_2500 theta
    · exact b3_1831 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1833 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3240 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2385 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1243 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2160 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3140 theta)
    · exact b3_2590 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_504 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1911 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3216 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2678 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_180 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2218 theta)
    · exact b3_3391 theta
    · exact b3_2703 theta
    · exact b3_61 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2067 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2066 theta)
    · exact b3_3404 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3398 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2387 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2145 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2133 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1256 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3407 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3142 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2590 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1911 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_504 theta)
    · exact b3_3216 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2594 theta)
    · exact b3_1954 theta
    · exact b3_1907 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_523 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3406 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3220 theta)
    · exact b3_2811 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1138 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1028 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1024 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3408 theta)
    · exact b3_3301 theta
    · exact b3_2895 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1442 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1442 theta)
    · exact b3_3342 theta
    · exact b3_23 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1133 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1124 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1126 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2963 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2953 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2952 theta)
    · exact b3_144 theta
    · exact b3_145 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1607 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1606 theta)
    · exact b3_3403 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2500 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1833 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1831 theta)
    · exact b3_3240 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2480 theta)
    · exact b3_2028 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2028 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3188 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2611 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_506 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1909 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3218 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2594 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_523 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1954 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1907 theta)
    · exact b3_3406 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3220 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2536 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2521 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_194 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2312 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2286 theta)
    · exact b3_3397 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2679 theta)
    · exact b3_179 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2217 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2216 theta)
    · exact b3_3405 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3399 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2471 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2030 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2039 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3179 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2385 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1243 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2160 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3140 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2383 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1241 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2147 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3138 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2703 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_61 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2067 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2066 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3404 theta)
    · exact b3_3398 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2678 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_180 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2218 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3391 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2611 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_506 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1909 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3218 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2387 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1256 theta)
    · exact b3_2145 theta
    · exact b3_2133 theta
    · exact b3_3407 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3142 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2679 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_179 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2217 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2216 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3405 theta)
    · exact b3_3399 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2536 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2521 theta)
    · exact b3_194 theta
    · exact b3_2312 theta
    · exact b3_2286 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3397 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2811 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1024 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1138 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1028 theta)
    · exact b3_3408 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3301 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2949 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_152 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1602 theta)
    · exact b3_3401 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2949 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_152 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1602 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3401 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2963 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2953 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2952 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_144 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_145 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1607 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1606 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1133 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1124 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1126 theta)
    · exact b3_3383 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3384 theta)
    · exact b3_3384 theta
    · exact b3_3385 theta
end Orbits1020Cost12
