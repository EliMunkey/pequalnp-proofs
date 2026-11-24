import Q1020K12L2S12Local
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S12
import Q1020K12L3S24
import Q1020K12L3S25
import Q1020K12L3S27
import Q1020K12L3S29
import Q1020K12L3S30
import Q1020K12L3S34
import Q1020K12L3S41
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S48
import Q1020K12L3S51
import Q1020K12L3S56
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S74
import Q1020K12L3S75
import Q1020K12L3S76
import Q1020K12L3S77
import Q1020K12L3S81
import Q1020K12L3S82
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_540 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_540 := by
  apply PetersenIndexedNode.close (bank := [s3_2391,a3972,a3973,s3_3146,s3_2477,a3974,a3975,s3_3185,a3976,a3977,a3978,a3979,s3_2506,a3980,a3981,s3_3439,a3982,a3983,a3984,a3985,s3_2598,a3986,a3987,s3_3444,a3988,s3_510,a3989,s3_3449,a3990,a3991,a3992,a3993,a3994,a3995,a3996,s3_3224,a3997,a3998,a3999,s3_3438,s3_2832,a4000,a4001,s3_3442,s3_2908,a4002,a4003,a4004,a4005,s3_3445,a4006,s3_1040,a4007,s3_3450,a4008,a4009,a4010,s3_3243,a4011,a4012,a4013,s3_3440,a4014,a4015,a4016,a4017,a4018,a4019,a4020,s3_3446,a4021,s3_1247,a4022,a4023,a4024,a4025,a4026,s3_3441,a4027,a4028,a4029,a4030,a4031,a4032,a4033,a4034,a4035,a4036,a4037,s3_3451,a4038,a4039,a4040,s3_3443,a4041,a4042,a4043,s3_3447,a4044,a4045,a4046,s3_3452,a4047,a4048,a4049,s3_3448,a1930,s3_1452,a4050,s3_3453,a4051,a4052,a4053,s3_3454]) (PetersenIndexedNode.reasons 256 17 448 0x8038311109010c4048037a1011911084048038b111191108444803721010901084048036280804202a0008035a10114100a0008036a80814100a0208035210104202210180341c0c042022101803392020c282610180349c0c0c282503080331202042022101803224040a08090008031a1011210090008032a404121009010803121010a080840480301404121005000802f92020a0805000803094040a0805010802f1202121004808802e0c444a0803101802d88404e0c02101802e8c444e0c02111802d08404a0802101802c2303050408c04802ba101191808404802ca30319180840c802b2101050408404802a120205040480080299404090804800802a92020908048088029140405040501080280a020908028008027884045040280080288a020504028088027084049080210180262622050402820802594100706038208026a622070602830802514100504028208024210100c0484008023a4041090084008024a1011090084048023240400c0406028022130300c040602802192021898048088022930318980480c8021120200c0406028020094140c042501801f884044c4421018020894144c442105801f084040c042101801e151100c040602801d941002c241602801e951102c240612801d141000c040602801c0b0900c040602801b8a0801c140e02801c8b0901c14060a801b0a0800c040602801a24848060203018019a101107028301801aa4849070290128019210100602030180179084806020301801712022005a480880189084a0060480a8016120200602030180150a828060203018014884044c48210180158a8284c48280a80140840406020301801324a0806020301801294100262213018013a4a08262203118012141000602030180110a8880602030180108a08016120b0180118a8881612030980100a08006020301800f0180806020600800ea12000c080600800f818080c080602800e2120006020301800d2141406040302800ca101107048302800da141507048405800c2101006040302800b1242406040302800a92020c2c04808800b92424c2c04809800a12020060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800100c044240030080008181006040300800180c040604030180000181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2391 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1253 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2163 theta)
    · exact b3_3146 theta
    · exact b3_2477 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2037 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2043 theta)
    · exact b3_3185 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2478 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2035 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2042 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3186 theta)
    · exact b3_2506 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1724 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1972 theta)
    · exact b3_3439 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2392 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1251 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2164 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3147 theta)
    · exact b3_2598 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_511 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1957 theta)
    · exact b3_3444 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2599 theta)
    · exact b3_510 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1958 theta)
    · exact b3_3449 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2395 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2156 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1260 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3150 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2607 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1914 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_516 theta)
    · exact b3_3224 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2925 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_306 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_525 theta)
    · exact b3_3438 theta
    · exact b3_2832 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1044 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1046 theta)
    · exact b3_3442 theta
    · exact b3_2908 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1454 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1453 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1459 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3456 theta)
    · exact b3_3445 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2835 theta)
    · exact b3_1040 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1143 theta)
    · exact b3_3450 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2502 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1836 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1838 theta)
    · exact b3_3243 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2484 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1728 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2047 theta)
    · exact b3_3440 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2609 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_514 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1916 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3225 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2602 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_521 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1919 theta)
    · exact b3_3446 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2402 theta)
    · exact b3_1247 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2153 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3157 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2483 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1727 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2048 theta)
    · exact b3_3441 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2397 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1259 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2158 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3152 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2400 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1248 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2151 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3155 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2604 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_519 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1921 theta)
    · exact b3_3451 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2860 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1149 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1726 theta)
    · exact b3_3443 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2924 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1254 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_347 theta)
    · exact b3_3447 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2859 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1263 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1730 theta)
    · exact b3_3452 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2837 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1041 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1142 theta)
    · exact b3_3448 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2910 theta)
    · exact b3_1452 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1457 theta)
    · exact b3_3453 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2968 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1049 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1052 theta)
    · exact b3_3454 theta
end Orbits1020Cost12
