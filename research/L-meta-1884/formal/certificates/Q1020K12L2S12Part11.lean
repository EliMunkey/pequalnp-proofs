import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S11
import Q1020K12L3S23
import Q1020K12L3S29
import Q1020K12L3S33
import Q1020K12L3S37
import Q1020K12L3S38
import Q1020K12L3S39
import Q1020K12L3S40
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S50
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S61
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S66
import Q1020K12L3S68
import Q1020K12L3S71
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
theorem b2_532 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_532 := by
  apply PetersenIndexedNode.close (bank := [s3_2366,a3470,a3471,s3_3127,s3_2466,a3472,a3473,s3_3174,a3474,a3475,a3476,a3477,s3_2498,s3_1827,a3478,a3479,a3480,a3481,a3482,a3483,s3_2573,a3484,a3485,a3486,a3487,a3488,s3_2694,s3_2693,s3_2686,s3_2685,a3489,a3490,a3491,a3492,a3493,a3494,s3_3355,s3_3349,a3495,s3_485,a3496,a3497,a3498,a3499,a3500,a3501,a3502,a3503,a3504,a3505,a3506,s3_3205,a3507,s3_1890,a3508,a3509,s3_2801,a3013,a2987,s3_3281,s3_2886,a3275,a3236,s3_3330,s3_21,s3_20,a3510,a2094,a3511,a3512,s3_977,a3513,a3514,a3515,a3516,a3517,s3_3238,a3518,s3_2011,a3519,a3520,a3521,a3522,a3523,a3524,a3525,a3526,a3527,a3528,a3529,a3530,a3531,a3532,a3533,a3534,s3_3356,s3_3350,a3535,s3_1221,a3536,a3537,a3538,a3539,a3540,a3541,a3542,a3543,a3544,a3545,a3546,a3547,a3548,a3549,a3550,a3551,a3552,a3553,a3554,a3555,a3556,a3557,a3558,a3559,a3560,a3561,a3562,a3563,a3564,a3565,a3566,a3567,a3568,a3569,a3570,a3571,s3_2116,a3572,a3573,a3574,a3575,a3576,s3_2223,s3_2222,a3577,a3578,a3579,a3580,a3581,a3582,a3583,a3584,a3585,a2957,a3271,a3400,a3273,a3586,s3_1412,a3587,a3454,a3020,a2471,a3021,a3588,a3589,a3590,a3209,a3591,a3592,s3_1688,s3_1687,a3593,a3594,s3_3357,s3_3354]) (PetersenIndexedNode.reasons 256 17 552 0x80562484a015692128055210120152840480572484a015a9212805421012014e84048052b1110840442028052210118504c2028053311118504c4448051a101084044202805140286014048088020c010084044202804f280805414a202804ea10114504a202804fa80814504a020804e2101054148404804dc026a013221018020c010054142101804b9888854146202804b10808c2824202804c18888c2824222804a90808541442028049a4040a080900080492101121009000804a24041210090108048a1010a08084048047402352100908080464022ca080504080484023ca08050408045402252100908080439484921005202804310808a0804202804414848a08042128042908092100420280418e868a0803a0a80410a828e0c02a0a80420e868e0c02a1a80408a828a0802a0a803fa303050408c04803f21011918084048040230319180840c803ea101050408404803d401e600f10077803b401d450402820803e401ec50402820803a401ce00e5007180379282850404a02803710808908042028038128289080420a8036908085040420280358a82890802a0280351850450402a0280360a82850402a0a803498504908048408033a6220504028208033141007060382080342622070602830803294100504028208031a10100c04840080312404109008400803221011090084048030a40400c040602802f4017509008480802e4016c0c04060280304017c0c040602802d4016509008480802b9d0d00c040602802b1080989804202802c1d0d189807034802a908080c0406028029995140c04060280290a8284c442602802a195144c44062280288a8280c0406028027951100c0406028027141002c2416028028151102c2406128026941000c04060280258b0900c04060280250a0801c140e0280260b0901c14060a80248a0800c0406028023a48484c48921280232101185808404802424849858092128022a10104c48840480224010e008403018020c01004c480301801f108084c484202801e9c0c084806220801f9080884804202801e1c0c04c48480a801d0a82884802a0a801c985044c482624801d8a8284c48280a801c185048480280a801b24a084c482624801a941006c683624801ba4a086c682634801a141004c48262480188a8884c482a2080180a082005e282080198a88a0064282280170a0804c482820801601808848006028015a12004c4826208016818084c48060280152120084804240801421414060403028013a1011070483028014a141507048405801321010060403028011c008a00430020800fc0078060403028012c009006040302800ec00720037001a800bc005806040302800a90808c2c04202800cc0060c2c02160800a10808060403028009185040604030280088a828424023028009985044240212080080a82806040302800714504060403028006941002624130280079450426240312800614100060403028005125040604030280048a08016140b028005925041614030a80040a08006040302800321604060403028002818084a4806028003a16044a48212480020180806040302800110d044240212080008989006040302800190d040604030280000989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2366 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1233 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2130 theta)
    · exact b3_3127 theta
    · exact b3_2466 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2023 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2026 theta)
    · exact b3_3174 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2468 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2025 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2025 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3176 theta)
    · exact b3_2498 theta
    · exact b3_1827 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1829 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3238 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2378 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1235 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2131 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3133 theta)
    · exact b3_2573 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_497 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1953 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1904 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3380 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3205 theta)
    · exact b3_2694 theta
    · exact b3_2693 theta
    · exact b3_2686 theta
    · exact b3_2685 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_36 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_39 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2321 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2326 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2315 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2318 theta)
    · exact b3_3355 theta
    · exact b3_3349 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2585 theta)
    · exact b3_485 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1905 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3214 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2380 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2116 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1236 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3135 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2573 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1953 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1904 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_497 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3380 theta)
    · exact b3_3205 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2587 theta)
    · exact b3_1890 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_500 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3213 theta)
    · exact b3_2801 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1000 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_994 theta)
    · exact b3_3281 theta
    · exact b3_2886 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1425 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1425 theta)
    · exact b3_3330 theta
    · exact b3_21 theta
    · exact b3_20 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1599 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1586 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1593 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2806 theta)
    · exact b3_977 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1004 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3292 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2498 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1829 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1827 theta)
    · exact b3_3238 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2469 theta)
    · exact b3_2011 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2011 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3177 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2588 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_499 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1902 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3211 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2587 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_500 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1890 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3213 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2706 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2709 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_25 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_28 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2223 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2222 theta)
    · exact b3_3356 theta
    · exact b3_3350 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2381 theta)
    · exact b3_1221 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2128 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3136 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2466 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2023 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2026 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3174 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2378 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1235 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2131 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3133 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2366 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1233 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2130 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3127 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2694 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2693 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2686 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2685 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_36 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_39 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2321 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2326 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2315 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2318 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3355 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3349 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2585 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_485 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1905 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3214 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2588 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_499 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1902 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3211 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2380 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1236 theta)
    · exact b3_2116 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3135 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2706 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2709 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_25 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_28 theta)
    · exact b3_2223 theta
    · exact b3_2222 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3356 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3350 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2381 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1221 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2128 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3136 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2801 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_994 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1000 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3281 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1681 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1673 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1678 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2891 theta)
    · exact b3_1412 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1426 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3336 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1599 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1586 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1593 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2806 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_977 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1004 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3292 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2989 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2991 theta)
    · exact b3_1688 theta
    · exact b3_1687 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_32 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_34 theta)
    · exact b3_3357 theta
    · exact b3_3354 theta
end Orbits1020Cost12
