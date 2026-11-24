import Q1020K12L2S12Local
import Q1020K12L3S12
import Q1020K12L3S24
import Q1020K12L3S27
import Q1020K12L3S29
import Q1020K12L3S30
import Q1020K12L3S34
import Q1020K12L3S42
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S51
import Q1020K12L3S56
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S65
import Q1020K12L3S67
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
theorem b2_538 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_538 := by
  apply PetersenIndexedNode.close (bank := [s3_2388,a3814,a3815,s3_3143,s3_2474,a3816,a3817,s3_3182,a3818,a3819,a3820,a3821,s3_2504,a3822,a3823,s3_3411,a3824,a3825,a3826,a3827,s3_2595,a3828,a3829,s3_3417,a3830,s3_507,a3831,s3_3422,a3832,a3833,a3834,a3835,a3836,a3837,a3838,s3_3221,a3839,s3_1848,a3840,s3_3412,s3_2828,a3841,a3842,s3_3415,s3_2904,a3843,a3844,s3_3418,a3845,s3_1035,a3846,s3_3423,a3847,a3848,a3849,s3_3241,a3850,s3_1974,a3851,s3_3413,a3852,a3853,a3854,a3855,a3856,a3857,a3858,s3_3419,a3859,s3_1244,a3860,a3861,a3862,a3863,a3864,s3_3414,a3865,a3866,a3867,a3868,a3869,a3870,a3871,a3872,a3873,a3874,a3875,s3_3424,a3876,a3877,a3878,s3_3416,a3879,a3880,s3_2070,s3_3420,a3881,s3_1265,a3882,s3_3425,a1007,a911,a964,s3_3421,a3883,s3_1449,a3884,s3_3426,a3885,a864,a3886,s3_3427]) (PetersenIndexedNode.reasons 256 17 448 0x803731110840442028036a4809850492028037b111185048444803624808840442028035280804202a0008034a48094100a0008035a80814100a0208034248084202210180331888842022101803290808c2826101803398888c282422280321080842022101803124808a08090008030a1011210090008031a480921009202803021010a0808404802f1080921005000802e92020a0805000802f90808a0804202802e1202121004808802d0a828a0803101802c88404e0c02101802d8a828e0c02a0a802c08404a0802101802b2682850409a02802aa480991809202802ba68299180920a802a24808504092028029120205040480080289080890804800802992020908048088028108085040420280270a020908028008026884045040280080278a020504028088026084049080210180252622050402820802494100544438208025a622054442a22802414100504028208023210100c0484008022a4809090084008023a1011090084048022248080c0406028021130300c040602802090809898042028021930318980480c8020108080c040602801f094140c042501801e884044c442101801f894144c442105801e084040c042101801d1511109005440801c941000c040602801d951100c040602801c1410109005040801b0b0900c040602801a8a0801c140e02801b8b0901c14060a801a0a0800c040602801924808062283018018a1011070283018019a480907029002801821010062290028017108080622420280169202185804808801790809858042028016120200622500280150a82806222a0a8014884044c68210180158a8284c682a0a80140840406222101801324a0907020301801294100062203018013a4a08062203118012141010702504080110a8880622031180108a08016320b1180118a8881632031980100a08006220311800f0180806220602800ea12000c280610800f818080c280602800e2120006220311800d2141406040302800ca480907049202800da141507048405800c2480806040302800b1242406040302800a90808c2c04202800b92424c2c04809800a10808060403028009084040604210080088a020424021008009884044240210180080a02006040302800714504424021208006941000604030280079450406040302800614100424021208005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800100c444240031080008185006040302800180c440604030280000185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2388 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1249 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2161 theta)
    · exact b3_3143 theta
    · exact b3_2474 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2033 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2041 theta)
    · exact b3_3182 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2475 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2034 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2040 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3183 theta)
    · exact b3_2504 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1801 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1839 theta)
    · exact b3_3411 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2389 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1250 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2162 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3144 theta)
    · exact b3_2595 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_508 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1955 theta)
    · exact b3_3417 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2596 theta)
    · exact b3_507 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1956 theta)
    · exact b3_3422 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2394 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2154 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1258 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3149 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2605 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1913 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_512 theta)
    · exact b3_3221 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2755 theta)
    · exact b3_1848 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_524 theta)
    · exact b3_3412 theta
    · exact b3_2828 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1043 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1042 theta)
    · exact b3_3415 theta
    · exact b3_2904 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1450 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1455 theta)
    · exact b3_3418 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2834 theta)
    · exact b3_1035 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1141 theta)
    · exact b3_3423 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2501 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1835 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1834 theta)
    · exact b3_3241 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2482 theta)
    · exact b3_1974 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2045 theta)
    · exact b3_3413 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2606 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_513 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1912 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3222 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2601 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_518 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1917 theta)
    · exact b3_3419 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2399 theta)
    · exact b3_1244 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2149 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3154 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2481 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1973 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2046 theta)
    · exact b3_3414 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2393 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1257 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2155 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3148 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2398 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1245 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2150 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3153 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2600 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_517 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1918 theta)
    · exact b3_3424 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2754 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_527 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1844 theta)
    · exact b3_3416 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2443 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1262 theta)
    · exact b3_2070 theta
    · exact b3_3420 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2406 theta)
    · exact b3_1265 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2148 theta)
    · exact b3_3425 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2833 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1038 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1140 theta)
    · exact b3_3421 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2905 theta)
    · exact b3_1449 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1456 theta)
    · exact b3_3426 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2967 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1047 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1048 theta)
    · exact b3_3427 theta
end Orbits1020Cost12
