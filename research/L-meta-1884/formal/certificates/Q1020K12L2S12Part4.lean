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
import Q1020K12L3S29
import Q1020K12L3S34
import Q1020K12L3S37
import Q1020K12L3S46
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S52
import Q1020K12L3S54
import Q1020K12L3S57
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S67
import Q1020K12L3S69
import Q1020K12L3S70
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
theorem b2_520 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_520 := by
  apply PetersenIndexedNode.close (bank := [a2874,a2875,a2876,a2877,a2878,a2879,s3_2532,s3_2526,s3_2517,a2880,a2881,a2882,a2883,a2884,a2885,a2886,s3_2668,a2887,a2888,s3_3279,a2889,a2890,a2891,s3_2821,a2892,a2893,a2894,a2895,a1024,a2086,s3_2958,s3_2957,s3_2932,a2896,a2897,a2898,a2899,s3_3281,s3_1122,a2900,a2901,a2902,a2903,a2904,a2905,a2906,a2907,a2908,a2909,a2910,a2911,s3_3283,a2912,a2913,a2914,a2915,a2916,a2917,a2918,a2919,a2920,a2921,a2922,a2923,a2924,a2925,a2926,a2927,a2928,s3_3285,a2929,a2930,a2931,a2932,a2933,a2934,s3_2062,a2935,a2936,a2937,s3_2206,s3_3287,a2938,a2939,a2940,a2941,a2942,a2943,a2944,a2945,s3_18,a2946,a2947,s3_1445,a2948,a2949,a2950,a2951,a2952,a2953,a2954,a2955,a2956,a2957,s3_3262,a2089,s3_3258,a2698,a2070,a2645,a2868,s3_3351,a2958,s3_1584,a2959,a2960,a2961,a2962,a2963,a2964,a2965,a2966,a2967]) (PetersenIndexedNode.reasons 256 17 510 0x14041007950102101200f084045010401e940408404803ba10118888622270102101200ea84046222401d98888840431112101200e90058210140168c44442024909401c9242484048038a10112425007349092101200e0840480374019a00db00218036401ae004b00678037c01aa00d30068311140198c445006580324018cc445006731114018a00c3006050104017940408404802ea10114041005f50102101200b88404802dc01645415005a80290a828c445005931114016200af0056802ac015084450053800c185060039005230a0a4040a0809000420224201200090104840240410808504042024014121009080802794100a0810051282014102009c908048401c0c121007020311114100e040703028201c0c0c4449080311140130a080504080259c180e0c1004d38301c18200945040282040120a080504080239c180e0c1004938301c182008c504028202303050408c0442023230108088c0c646021031080828204202401120087004280208a0805041004514100a0820081003f801f400f050402820311112100d041003d242012100c44428201410400e890804840801c8a0805041003b14100a082007048402420400d890804840801a8a0805041003714100a082006848402420262205040282028200e0c0704098881c180a0c0a08028201410210100c04840048082120108008404424021011202006020301400c80c0406028018898884c45003313110988a0060060203011d0d00c040602311131300c444743462601c0d0c44406020301400b9090084808016818080c05002f03010180a005884804240400a80c0406028014898884c45002b13110988a005006020301151100c0406022820058482c0454440b0901848a080060203010b0900c0406021410038281c042c24070501828504006020301248484c489212420240099080892128013a484908082624420240092004700228010898904c4900251312098920041001f800f188884c486220381818980c4406222313018888e060262413124007600340301800e098900603001b800d400660030262413124005e002c42604941098904c4850401b1a0d89125043634131a141004c48262415110989054402820800a0a0805445001514110a0804c4828200301189800c0484801312098800c042624030121200c4c06260428280c080604840441c120c090a0a83824202a101006040302800900c08060500111090084820026212010904004006040302800700c080604622230b018482001e616010b0188880604030280064002e00150009018100c0a001a0302018140022000f0006800200c0806050003109008482000a21201090400080604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030280000848042402624018100c0a0002030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b3_2140 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3300 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2405 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1239 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2139 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3395 theta)
    · exact b3_2532 theta
    · exact b3_2526 theta
    · exact b3_2517 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_190 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2302 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2303 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2282 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3285 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1950 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3296 theta)
    · exact b3_2668 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_174 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2214 theta)
    · exact b3_3279 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1950 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3296 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2824 theta)
    · exact b3_2821 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1013 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1133 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_945 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1126 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_18 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_944 theta)
    · exact b3_2958 theta
    · exact b3_2957 theta
    · exact b3_2932 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_132 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1595 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1566 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1588 theta)
    · exact b3_3281 theta
    · exact b3_1122 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_3301 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2592 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_502 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1933 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3373 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2676 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_172 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2206 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3287 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2699 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_57 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2062 theta)
    · exact b3_3283 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2405 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1239 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2139 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3395 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2668 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_174 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2214 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3279 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2140 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3300 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2532 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2526 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2517 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_190 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2302 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2303 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2282 theta)
    · exact b3_3285 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2592 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_502 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1933 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3373 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2699 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_57 theta)
    · exact b3_2062 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3283 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2676 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_172 theta)
    · exact b3_2206 theta
    · exact b3_3287 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_23 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_998 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2821 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2824 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1133 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1126 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_945 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1013 theta)
    · exact b3_18 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_998 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2903 theta)
    · exact b3_1445 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1433 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3400 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2958 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2932 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2957 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1595 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1588 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1566 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_132 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3281 theta)
    · exact b3_3262 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3258 theta)
    · exact b3_3258 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_129 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_134 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_129 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_134 theta)
    · exact b3_3351 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2945 theta)
    · exact b3_1584 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_128 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3292 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_944 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1122 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3301 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2945 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1584 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_128 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3292 theta)
end Orbits1020Cost12
