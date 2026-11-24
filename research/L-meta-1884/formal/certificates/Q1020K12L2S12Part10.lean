import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S33
import Q1020K12L3S39
import Q1020K12L3S46
import Q1020K12L3S52
import Q1020K12L3S63
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S79
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_530 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_530 := by
  apply PetersenIndexedNode.close (bank := [a3406,a3407,s3_2657,a3408,a3409,a3410,a3411,s3_3339,a3412,s3_217,a3413,s3_3335,a3414,a3415,s3_1942,a3416,a2040,s3_2901,a3417,a3418,a784,a2028,s3_2973,s3_262,a3419,s3_3336,a3420,a3421,a3422,a3423,a3424,a3425,a3426,a3427,a3428,a3429,a3430,a3431,a3432,a3433,a3434,a3435,a3436,a3437,a3438,a3439,a3440,a3441,a3442,a3443,a3444,a3445,s3_2196,a3446,a3447,a3448,a3449,a3450,a3451,a3452,a3453,a3454,a3455,a3456,s3_1408,a3457,s3_19,a3401,a1153,a3458,a3459,a3460,a3461,a3462,s3_1677,a3463,a3464,s3_3325,a3465,s3_3324,s3_287,s3_288,s3_286,a3466,a3467,a3468,s3_3357,a3469,s3_3337,s3_1407]) (PetersenIndexedNode.reasons 256 17 510 0x200b3004042024010940408404802ac015200a700528028c014200b10057802b4013e009d004d51114012d4444a0208025280814445004c5111280820092a0208023908088405004631111888a00906222311140114840442027030108088404a020614128081c0c0c282703028080840442028022400489011001421011080a008700411080c01094100210150104010540410040504028202007f003e4212400f14100a080801da8a094505003d514128a0a0074a08050401888941006222210138300840462227060188888404a0802101400e0a0805040801b9c180e0c1003938301c182006c504028202c0c0a080b0205010242014040b0304840280c1404050405010400d121009080801994100a0810035282014102006490804840148492100520221011410084045212282010848840490802101400c0a080504050401c180e0c1003138301c181410050402820400b89080484080168a0805041002f14100a082005848402420400a8504028205010323014041002b646032301404028201410400a05040282080138a8885445002915110a88a004c282014101282850404a0221011210084044a0a2420108288404282021012a2209080484050400a0805040a88814100a081410048402420262205040282028200e0c0704098881c180a0c0a08028201410400900c0406028011898884c45002513110988a004406020301290900c0406025010212014040a4244240280914040060203014008109008480800f818080c05002103010180a003c84804240400700c0406022101313008405001d626031300840406020301400680c0406025040098884c45001b131109889410006020301151100c0406022820058482c0454440b0901848a080060203010b0900c0406021410038281c042c240705018285040060203014006084804240800b98980c4c10019313018982002c42402120288888480a222501030b014040a2226160288894040424050104005600260301800a109000602420280099080a002442402120400460020480a5141109008480a0803130189814504626031302820084804240494110900848050408007141012505000f494114100848042401511109005444282080060a0805445000d15110a080848028200301109000c0484802322119000c04464403012120084804240800500c08060500091090084820016212010904002006040302800300c080604a02041c128082000e838241c1280800604030280020848042410003018100c0a000a030201814000842402120800000c080604420230b01080a0002616030b0108080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c088682030201811090042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b3_1942 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3339 theta)
    · exact b3_2657 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_217 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2196 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3335 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1942 theta)
    · exact b3_3339 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2657 theta)
    · exact b3_217 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2196 theta)
    · exact b3_3335 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1942 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3339 theta)
    · exact b3_1942 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_3339 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2901 theta)
    · exact b3_2901 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1408 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1408 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_19 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1407 theta)
    · exact b3_2973 theta
    · exact b3_262 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1677 theta)
    · exact b3_3336 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1942 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3339 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1942 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3339 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2657 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_217 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2196 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3335 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2657 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_217 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2196 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3335 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2657 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_217 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2196 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3335 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1942 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3339 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2657 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_217 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2196 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3335 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1942 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3339 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2657 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_217 theta)
    · exact b3_2196 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_3335 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2657 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_217 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2196 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3335 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2973 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_262 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1677 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3336 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2901 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2901 theta)
    · exact b3_1408 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1408 theta)
    · exact b3_19 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1407 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1407 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2973 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_262 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1677 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3336 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2973 theta)
    · exact b3_1677 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_262 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3336 theta)
    · exact b3_3325 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3324 theta)
    · exact b3_3324 theta
    · exact b3_287 theta
    · exact b3_288 theta
    · exact b3_286 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_287 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_286 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_288 theta)
    · exact b3_3357 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3337 theta)
    · exact b3_3337 theta
    · exact b3_1407 theta
theorem b2_531 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_531 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_531 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
