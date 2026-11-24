import Q1020K12L2S12Local
import Q1020K12L3S8
import Q1020K12L3S12
import Q1020K12L3S24
import Q1020K12L3S25
import Q1020K12L3S27
import Q1020K12L3S29
import Q1020K12L3S30
import Q1020K12L3S34
import Q1020K12L3S40
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
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_539 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_539 := by
  apply PetersenIndexedNode.close (bank := [s3_2390,a3887,a3888,s3_3145,s3_2476,a3889,a3890,s3_3184,a3891,a3892,a3893,a3894,s3_2505,a3895,a3896,s3_3429,a3897,a3898,a3899,a3900,s3_2597,a3901,a3902,s3_3432,a3903,s3_509,a3904,a3905,a3906,a3907,a3908,a3909,a3910,a3911,a3912,s3_3223,s3_2861,a3913,a3914,s3_3428,s3_2830,a3915,a3916,s3_3431,s3_2906,a3917,a3918,s3_3433,a3919,s3_1039,a3920,a3921,a3922,a3923,a3924,s3_3242,a3925,a3926,a3927,s3_3430,a3928,a3929,a3930,a3931,a3932,a3933,a3934,s3_3434,a3935,s3_1246,a3936,a3937,a3938,a3939,a3940,a3941,a3942,a3943,a3944,a3945,a3946,a3947,a3948,a3949,a3950,a3951,a3952,a3953,a3954,a3955,a3956,a3957,a3958,a3959,a3960,s3_3435,a3961,s3_1264,a3962,a3963,a3964,a3965,a3966,s3_3436,a3967,s3_1451,a3968,a3969,a1797,a3970,a3971,s3_3437]) (PetersenIndexedNode.reasons 256 17 448 0x803731110840442028036a10118504c2028037b111185048444803621010840442028035280804202a0008034a10114100a0008035a80814100a0208034210104202210180331888842022101803290808c2826101803398888c282522280321080842022101803124040a08090008030a1011210090008031a404121009010803021010a0808404802f1404121005000802e90808a0805000802f94040a0805010802e1080921004202802d0c444a0803101802c88404e0c02101802d8c444e0c02111802c08404a0802101802b2303050408c04802aa101191808404802ba30319180840c802a21010504084048029120205040480080289080890804800802992020908048088028108085040420280270a020908028008026884045040280080278a020504028088026084049080210180252622050402820802494100544438208025a622054442a22802414100504028208023210100c0484008022a4041090084008023a1011090084048022240400c0406028021130300c040602802090809898042028021930318980480c8020108080c040602801f094140c042501801e884044c442101801f894144c442105801e084040c042101801d151100c040602801c941002c241602801d951102c240612801c141000c040602801b0b0900c040602801a8a0801c140e02801b8b0901c14060a801a0a0800c040602801924848060203018018a1011070283018019a484907029012801821010060203018017108080602420080169202084804200801790808848042028016120200602030180150a868060203018014884044c68210180158a8684c68280a80140840406020301801324a0806020301801294100262213018013a4a08262203118012141000602030180110a8880602030180108a08016120b0180118a8881612030980100a08006020301800f0180806020600800ea12000c080600800f818080c080602800e2120006020301800d2141406040302800ca101107048302800da141507048405800c2101006040302800b1242406040302800a90808c2c04202800b92424c2c04809800a10808060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800100c044240030080008181006040300800180c040604030180000181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2390 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1252 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2165 theta)
    · exact b3_3145 theta
    · exact b3_2476 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2036 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2044 theta)
    · exact b3_3184 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2476 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2036 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2044 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3184 theta)
    · exact b3_2505 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1701 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2180 theta)
    · exact b3_3429 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2390 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1252 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2165 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3145 theta)
    · exact b3_2597 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_509 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1959 theta)
    · exact b3_3432 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2597 theta)
    · exact b3_509 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1959 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3432 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2396 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2157 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1261 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3151 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2608 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1915 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_515 theta)
    · exact b3_3223 theta
    · exact b3_2861 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_337 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_526 theta)
    · exact b3_3428 theta
    · exact b3_2830 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1045 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1045 theta)
    · exact b3_3431 theta
    · exact b3_2906 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1451 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1458 theta)
    · exact b3_3433 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2836 theta)
    · exact b3_1039 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1144 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3436 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2503 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1837 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1837 theta)
    · exact b3_3242 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2485 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1700 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2049 theta)
    · exact b3_3430 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2608 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_515 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1915 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3223 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2603 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_520 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1920 theta)
    · exact b3_3434 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2401 theta)
    · exact b3_1246 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2152 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3156 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2485 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1700 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2049 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3430 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2396 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1261 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2157 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3151 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2401 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1246 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2152 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3156 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2603 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_520 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1920 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3434 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2861 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_526 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_337 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3428 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2858 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1264 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1699 theta)
    · exact b3_3435 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2858 theta)
    · exact b3_1264 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1699 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3435 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2836 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1039 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1144 theta)
    · exact b3_3436 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2906 theta)
    · exact b3_1451 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1458 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3433 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2969 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1051 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1051 theta)
    · exact b3_3437 theta
end Orbits1020Cost12
