import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S9
import Q1020K12L4S12
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S20
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S24
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S39
import Q1020K12L4S41
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S49
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S71
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc26w0 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl


private theorem pc26w4 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w3 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w4 stored0 rfl rfl






private theorem pc32w11 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl


private theorem pc32w15 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 stored25 stored26 rfl rfl
private theorem pc32w14 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w15 stored24 rfl rfl




private theorem pc26w23 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w23 stored0 rfl rfl


private theorem pc30w24 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl


private theorem pc30w28 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w27 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffff55005500ffffffff55005500 := PetersenWireProjection.derive 3 pc30w28 stored8 rfl rfl




private theorem pc26w36 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w36 stored0 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w38 stored0 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfffffffffffffffffffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w42 stored0 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w45 stored0 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xfafafafafafafafaf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w47 stored0 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffffffffffffffffafafafafafafafa := PetersenWireProjection.derive 3 pc26w49 stored0 rfl rfl
private theorem pc30w51 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w50 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xffffffffaa00aa00ffffffffaa00aa00 := PetersenWireProjection.derive 3 pc30w51 stored8 rfl rfl


private theorem pc0w53 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w52 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w53 stored49 rfl rfl







private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl

private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w66 stored33 rfl rfl







private theorem pc41w73 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl

private theorem pc41w76 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl
private theorem pc41w79 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored89 stored95 rfl rfl
private theorem pc41w78 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w79 stored91 rfl rfl





private theorem pc26w85 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w0 pc26w38 rfl rfl
private theorem pc30w87 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w86 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfffffffff000f000fffffffff000f000 := PetersenWireProjection.derive 3 pc30w87 stored8 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff000f000fffffffff000f000 := PetersenWireProjection.derive 3 pc30w24 pc30w87 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w90 stored0 rfl rfl
private theorem pc30w91 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w92 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w94 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffaaffaaffffffffffaaffaa := PetersenWireProjection.derive 3 pc30w94 stored8 rfl rfl
private theorem pc30w95 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w97 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w96 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w97 stored8 rfl rfl
private theorem pc30w99 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w98 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 pc30w99 stored8 rfl rfl
private theorem pc32w100 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w102 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w101 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc32w102 stored24 rfl rfl
private theorem pc32w103 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored24 stored29 rfl rfl


private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl


private theorem pc34w108 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w107 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w108 stored16 rfl rfl
private theorem pc34w111 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl




private theorem pc41w116 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl
private theorem pc41w118 : PetersenPackedPin.project extra41 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored90 stored95 rfl rfl
private theorem pc41w117 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w118 stored91 rfl rfl
theorem b3_3360 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3360 := by
  apply PetersenIndexedNode.close (bank := [a6055,s4_2930,s4_1497,a6056,a5688,s4_2982,a6057,a6058,s4_98,a6059,a6060,a6061,a6062,a6063,a6064,s4_2931,a6065,a6066,s4_1650,a6067,a6068,a6069,a6070,s4_2070,a6071,a6072,a6073,a6074,a6075,a6076,a6077,a6078,s4_2925,a6079,a6080]) (PetersenIndexedNode.reasons 256 17 426 0x12425001c42024002188888404490931111242500228010c0082003f001e6101248498504c2026222400758889001c614130a098888c28242224006e003484445111084044202921230a0a880944446141511124848420221017030084044202c44415050a829c0c02a0a15053111042022101800c084044202c28230a0985060032614130a0b0a084202210149094005d2404a2222820248092424504049092888a002ca222800a14100a080c444484034102002a9080484031110a08050408009242012100c28228201410200265040282030a09210090801888941006202210138300840462227060108888404a08021014d0d0a0813424921224202484934344840490d248485040921280080a0805040c44415110a88a00222a221511311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e08131103830141814100504028208007018080c04921242402180a001e84804240248480c0406026222400358880e060030101809888806020301381820018e0608005018080c04c2826260312020016c4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490940025242500082120109012424424048094001e000c90128002109000602c44441c080c06000a838141c0b111084804240614120e058500c88821201090185044240212032221070283811505109005414210131300840454146260150508404848021014941109008480504080011410125050003484114100848042401511109005444282045c48a08054448b8915110a080848028200301109000c0484802322119000c04464403012120084804240800000c080604921230b020c0a0002616030b0248480604030262a2884804240c444018100c098a8a03020181311104240212064c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c088682030201811090042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1591 theta)
    · exact b4_2930 theta
    · exact b4_1497 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2994 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact b4_2982 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2739 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2727 theta)
    · exact b4_98 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1109 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1500 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2992 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2275 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1747 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1803 theta)
    · exact b4_2931 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1527 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2958 theta)
    · exact b4_1650 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2993 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1668 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2979 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2361 theta)
    · exact b4_2070 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_784 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2991 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2623 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2614 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_705 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1108 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_730 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_729 theta)
    · exact b4_2925 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2897 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2799 theta)
theorem b3_3361 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3361 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(3,true))] s3_3361 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf5f5f5f5f5f5f5f5f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons pc26w0 rfl))))))))) (by decide +kernel)
theorem b3_3362 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3362 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(3,true))] s3_3362 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w14 (PetersenWireProjection.cons pc32w11 rfl))))))))) (by decide +kernel)
theorem b3_3363 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3363 := by
  apply PetersenIndexedNode.close (bank := [a6081,s4_2933,a6082,a6083,a6084,a6085,a6086,a6087,a6088,s4_2934,a6089,a6090,s4_1651,a6091,a6092,a6093,a6094,s4_2071,a6095,a6096,a6097,a6098,a6099,a6100,a6101,a6074,a6075,a6102,a6103,a6104,s4_2925,a6079,a6105]) (PetersenIndexedNode.reasons 256 17 426 0x14041001a4202400598888840450103111140410020800fc007a003b001c2101280818504420262224006d8889001a614130a098888c2824222400660030844450104005d4041001630a09850540406141501040056002884247030185044202c444504008405c0c0a080703031110c28261418009282014100c28230a0985060026614130a0b0a094100a0805818400456040a020282028081606050405018280820020a020800714100a080c444484034102001e9080484031110a08050408006242012100c282282014102001a5040282030a0921009080800514100a080614138301c10200167060283018504a080504080040a0805040a02024202808200124840242028080504028208003121009080c44414100a082000e28201410311109080484064440a0805040c28224201210191104840242030a08504028205444121009080614114100a08151102820141018504908048404c440a080504050401c180e08131103830141814100504028205212018080c04a020424028081484884805012280800c0406026222018080c04e060131109889888826221311381800c0406028002018080c04c282626031202000ac4c0426030a080c04060232a2818080c046141131109888ca8a26221311185040c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602511100c040602a0202120280814444424050112808006020301800100c040602c4441312098920006262413123111006020301614100c040602c8882120109018504424021203222006020301514100c04060261411312098914504262413121850406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800000c080604a02030b0280820002616030b0280800604030262a280c080604c4441090084818a8a21201090311100604030264c480c080604c28230b0185819312616030b030a080604030230a080c080604a080109008480c28221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1592 theta)
    · exact b4_2933 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_840 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2983 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1499 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2989 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1530 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2957 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1809 theta)
    · exact b4_2934 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1503 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3017 theta)
    · exact b4_1651 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2990 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1666 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2978 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2362 theta)
    · exact b4_2071 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_785 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2988 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2738 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2724 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_102 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1098 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2622 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2614 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_705 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1160 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_735 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_734 theta)
    · exact b4_2925 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2897 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2812 theta)
theorem b3_3364 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3364 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(3,true))] s3_3364 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons pc26w0 rfl))))))))) (by decide +kernel)
theorem b3_3365 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3365 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(0,true),(6,true))] s3_3365 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff55005500ffffffff55005500,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons pc30w24 rfl))))))))) (by decide +kernel)
theorem b3_3366 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3366 := by
  apply PetersenIndexedNode.close (bank := [a6106,s4_2954,a6107,s4_2942,s4_2782,s4_2772,s4_205,a6108,a6109,a6110,a6111,s4_2943,a6112,a6113,a6114,a6115,a6116,a6117,a6118,a4642,s4_963,a6119,a6120,a6121,a6122,s4_2947,s4_2925,a4643,a6123]) (PetersenIndexedNode.reasons 256 17 426 0x124250014420240019404084044909280812425001c800dc006a00304202210124848c444c202800c98888c4449212210110809c0c04808240428080840442027030108088404a020240412022002f00161080a484941002101501040055404100145040282014040a08050104004e00248424311128200c4444202706010808c444e0c0311110809410042024909141012405001138302480924247060490940040a08050405818141016040a02048402808160609080501828080a080a020280824200a0004202282014000a020504028081080921004202800714100a080a08038301c182001e7060383028200a08050404d0d121013424921214102484934342820490d248489080921280060a0805040a020646028082001ac8c06460280805040282024040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028208005018080c04921213112180a001626221311248480c0406025212098894840a020030101809484806020301280804c44a0202606018080c0442026260108089818c4c02406108080c0406028004018080c04a08013110988a001226221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060249094001d2425000613120989124242624480940016000890125111098900602a02041c080c05444483815011280804c48a02021010989084044808313012020840462602101120204c484808514120e054500a080131209891450426241312282010702a0804941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260800100c0806049212109020c0a00062120109024848060403028000084804240a020018100c0a0002030201812808042402120248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c090702030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b4_1536 theta)
    · exact b4_2954 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1780 theta)
    · exact b4_2942 theta
    · exact b4_2782 theta
    · exact b4_2772 theta
    · exact b4_205 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1162 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1505 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3015 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1771 theta)
    · exact b4_2943 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1533 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2956 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1504 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3016 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2434 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_181 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2690 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2669 theta)
    · exact b4_963 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1096 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_966 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_965 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1161 theta)
    · exact b4_2947 theta
    · exact b4_2925 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2911 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2824 theta)
theorem b3_3367 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3367 := by
  apply PetersenIndexedNode.close (bank := [a6124,s4_2945,a5688,s4_2982,a6125,s4_99,a6126,a6127,a6128,s4_2946,a6129,a6130,s4_1652,a6131,a6132,a6133,a6134,a6135,a6136,s4_145,s4_2072,a6137,a6138,a6139,s4_2947,a6140,a6141,a6142,a6143,a6144,a6145,s4_2937,a6146,s4_2938,s4_20]) (PetersenIndexedNode.reasons 256 17 426 0x12425001b420240089888884044909311112425002180104007e003d001d210124848850442026222400718889001b214110a098888428242224006a00328444800b884044202921230a0a880a0030614130a0a4848420221017030084044202c444504038101c0c0a08015053111042022101800a884044202428230a098506002c614130a090a0842022101490940051240500132820248092424504049094004a00230010800714100a080c444484034102001e9080484031110a080504080062420121004282282014102001a5040282010a09210090801888941006202210138300840462227060108888404a08021014d0d0a0813424921224202484934344840490d248485040921280050a0805040c4446460321020016c8c02460311105040282064440a0805040428224201210191104840242010a08504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e08131103830141814100504028208004018080c04921242402180a001284804240248480c0406026222098884c44e060030101809888806020301381804c4426228003018080c044282626031202000ec4c0426010a080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060249090989124250005313018981242462604809400104c4890128001098900602c44441c080c060006838141c0b11104c4826242141098904c48c888313018980850462603130322204c482624514120e044602210113120840545042624131208405070221014941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260800000c080604921230b020c0a0002616030b0248480604030262a2884804240c444018100c098a8a03020181311104240212064c480c080604428230b0185819312616030b010a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c090702030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1590 theta)
    · exact b4_2945 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact b4_2982 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2726 theta)
    · exact b4_99 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1498 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2996 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1804 theta)
    · exact b4_2946 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1534 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2955 theta)
    · exact b4_1652 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2997 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1754 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2977 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2360 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2359 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2349 theta)
    · exact b4_145 theta
    · exact b4_2072 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_783 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2995 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1097 theta)
    · exact b4_2947 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2628 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2627 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_526 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_834 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_744 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_743 theta)
    · exact b4_2937 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2940 theta)
    · exact b4_2938 theta
    · exact b4_20 theta
theorem b3_3368 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3368 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,false)),(false,(0,true),(3,true))] s3_3368 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w35 rfl))))))))) (by decide +kernel)
theorem b3_3369 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3369 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true))] s3_3369 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w37 rfl))))))))) (by decide +kernel)
theorem b3_3370 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3370 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,true)),(false,(0,true),(5,true))] s3_3370 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w39 rfl))))))))) (by decide +kernel)
theorem b3_3371 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3371 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(7,true))] s3_3371 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons pc26w40 rfl)))))))))) (by decide +kernel)
theorem b3_3372 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3372 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,false),(7,true))] s3_3372 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons pc26w41 rfl)))))))))) (by decide +kernel)
theorem b3_3373 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3373 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_3373 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b3_3374 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3374 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(0,false),(1,true))] s3_3374 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffffafafffffafafffffafafffffafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons pc26w44 rfl)))))))))) (by decide +kernel)
theorem b3_3375 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3375 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false)),(false,(0,true),(3,true))] s3_3375 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafaf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w46 rfl))))))))) (by decide +kernel)
theorem b3_3376 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3376 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(3,true))] s3_3376 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w40 rfl))))))))) (by decide +kernel)
theorem b3_3377 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3377 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,true),(0,false))] s3_3377 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons pc26w41 rfl)))))))))) (by decide +kernel)
theorem b3_3378 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3378 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(3,true),(7,true))] s3_3378 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b3_3379 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3379 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(1,true),(0,false))] s3_3379 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0,0xfffffffffffffffffafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons pc26w48 rfl)))))))))) (by decide +kernel)
theorem b3_3380 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3380 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,false),(3,true))] s3_3380 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w0 (PetersenWireProjection.cons pc26w41 rfl))))))))) (by decide +kernel)
theorem b3_3381 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3381 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(3,false)),(false,(0,true),(6,true))] s3_3381 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffaa00aa00ffffffffaa00aa00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w50 (PetersenWireProjection.cons pc30w24 rfl))))))))) (by decide +kernel)
theorem b3_3382 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3382 := by
  apply PetersenIndexedNode.close (bank := [a6147,s4_2965,a6148,a6149,a5688,s4_2982,a6150,s4_100,a6151,a6152,a6153,s4_2966,a6154,a6155,a6156,s4_2967,s4_1653,a6157,a6158,a6159,a6160,s4_2077,a6161,a6162,a6163,a6164,a6165,a6166,a6167,a6168,a6169,a6170,s4_2959,a6171,s4_2960,s4_65]) (PetersenIndexedNode.reasons 256 17 426 0x14445001c42024008d88888404511131111444500228010c0082003f001e210128889850442026222400758889001c614130a098888c28242224006e003484445111084044203001930a09850544446141511140060420221017030084044202c44450400a829c0c0a08070303111042022101800b084044202c28230a098506002e614130a0b0a08420221015919400556444a2222820288896464504051192888a0028a222800914100a080c44448403410200269080484031110a08050408008242012100c28228201410200225040282030a09210090801888941006202210138300840462227060108888404a080210180070a0805040a22224202888a001e48402420288885040282080060a0805040c44415110a88a001a2a221511311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e08131103830141814100504028208005018080c04a22242402888a001684804240288880c0406026222018080c04e060131109889888826221311381800c0406028004018080c04c2826260312020012c4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602511100c04060300072120109014444424050114001806020301800200c040602c44441c089892000a838141c0b111006020301614100c040602c8882120109018504424021203222006020301514100c04060221018001084054505000314050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800000c080604a22230b02888a0002616030b0288880604030262a280c080604c444119108c898a8a23221191311100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1593 theta)
    · exact b4_2965 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_791 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3001 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact b4_2982 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2728 theta)
    · exact b4_100 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1501 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2999 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1805 theta)
    · exact b4_2966 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1579 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2980 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1810 theta)
    · exact b4_2967 theta
    · exact b4_1653 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3000 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1761 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2981 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2365 theta)
    · exact b4_2077 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_792 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2998 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2725 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_103 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2713 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2712 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_218 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1018 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_773 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_772 theta)
    · exact b4_2959 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2962 theta)
    · exact b4_2960 theta
    · exact b4_65 theta
theorem b3_3383 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3383 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3383 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w52 rfl)))))))) (by decide +kernel)
theorem b3_3384 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3384 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3384 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons pc3w62 rfl))))))))) (by decide +kernel)
theorem b3_3385 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3385 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_3385 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w78 (PetersenWireProjection.cons pc41w76 (PetersenWireProjection.cons pc41w73 rfl)))))))))) (by decide +kernel)
theorem b3_3386 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3386 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true))] s3_3386 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons pc26w85 rfl))))))))) (by decide +kernel)
theorem b3_3387 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3387 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(0,true),(6,true))] s3_3387 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff000f000fffffffff000f000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons pc30w24 rfl))))))))) (by decide +kernel)
theorem b3_3388 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3388 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(0,true),(6,true))] s3_3388 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff000f000fffffffff000f000,0xfffffffff000f000fffffffff000f000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons pc30w88 rfl))))))))) (by decide +kernel)
theorem b3_3389 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3389 := by
  apply PetersenIndexedNode.close (bank := [a6172,s4_2986,a6173,s4_180,a6174,s4_2971,s4_2773,s4_206,a6175,s4_2973,a6176,a6177,a6178,a6179,a6180,s4_2975,a6181,a6182,a6183,a6184,a6185,a6186,a6187,a6188,a6189,a6190,a6191,a6192,a6193,a6194,s4_405,a6195,s4_4,a6196,a6197,a6198,a6199,a6200,a6201,s4_2959,s4_2963,s4_2961,s4_193,s4_404,s4_2972]) (PetersenIndexedNode.reasons 256 17 426 0x20057001e4202400a9404084048016280814041002980144009e004a4808240440090e060703080131c0c0e0610023240412021c0c0480821012808185044202703030a0940c0a020240412022004500211080c00814100210150104007d4041001e5040282014040a08050104007600388424381828200e0604808706012020e060e0c038181202141004808800d14100a081001938301c18200367060383040060a08050405818141016040a02048402808160609080501828080a080a020280824200a0004808282014000a020504028081202121004808800b14100a080a08038301c182002e7060383028200a0805040800a121009081001314100a082002a28201410400489080484080080a0805040a0206460280820022c8c06460280805040282024040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028208007018080c05000d13110988a001e26221311400300c0406025212018080c04a020424028081484884805012280800c0406022606018080c0448086260120209818c4c02406120200c0406028005018080c04a08013110988a001626221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800400c04060300071312098920012262413124001806020301511100c040602a02041c0a80814444838150112808006020301614100c04060248086160120218504c2c024051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800200c0806050003109008482000a212010904000806040302800000c080604a02041c1280820002838241c12808006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1581 theta)
    · exact b4_2986 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2424 theta)
    · exact b4_180 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1781 theta)
    · exact b4_2971 theta
    · exact b4_2773 theta
    · exact b4_206 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1168 theta)
    · exact b4_2973 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1506 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3018 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2435 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_182 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1772 theta)
    · exact b4_2975 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1581 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2986 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2424 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_180 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1781 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2971 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1506 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3018 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2435 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_182 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1772 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2975 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2721 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2715 theta)
    · exact b4_405 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1028 theta)
    · exact b4_4 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_972 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_971 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2773 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_206 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1168 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2973 theta)
    · exact b4_2959 theta
    · exact b4_2963 theta
    · exact b4_2961 theta
    · exact b4_193 theta
    · exact b4_404 theta
    · exact b4_2972 theta
theorem b3_3390 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3390 := by
  apply PetersenIndexedNode.close (bank := [a6202,s4_2987,a6203,s4_169,a6204,s4_2974,s4_2791,s4_21,a6175,s4_2973,a6205,a6206,a6207,a6208,a6209,s4_2976,a6210,a6211,a6212,a6213,a6214,a6215,a6216,a6217,a6218,a6219,a6220,a6221,a6222,a6223,s4_406,a6224,s4_4,a6225,a6226,a6227,a6200,a6201,s4_404]) (PetersenIndexedNode.reasons 256 17 417 0x10026800f210120040a0204202400909010480880119c0c0e061002538181c0c20044480824043818090104808501010a094040e06021412818140404808240440086003e21018010282004202a020800fa8082003ca08050404007600388424381828200e0604808706012020e060e0c038181202141004808800d14100a081001938301c18200367060383040060a08050405818141016040a02048402808160609080501828080a080a020280824200a0004808282014000a020504028081202121004808800b14100a080a08038301c182002e7060383028200a0805040800a121009081001314100a082002a28201410400489080484080080a0805040a0206460280820022c8c06460280805040282024040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028208007018080c05000d13110988a001e26221311400300c0406025212018080c04a020424028081484884805012280800c0406022606018080c0448086260120209818c4c02406120200c0406028005018080c04a08013110988a001626221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800400c04060300071312098920012262413124001806020301511100c040602a02041c0a80814444838150112808006020301214100c0406024808216012020850442c024051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800200c0806050003109008482000a212010904000806040302800000c080604a02041c1280820002838241c12808006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1582 theta)
    · exact b4_2987 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2463 theta)
    · exact b4_169 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1824 theta)
    · exact b4_2974 theta
    · exact b4_2791 theta
    · exact b4_21 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1168 theta)
    · exact b4_2973 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1507 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3019 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2464 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_170 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1823 theta)
    · exact b4_2976 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1582 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2987 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2463 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_169 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1824 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2974 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1507 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3019 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2464 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_170 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1823 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2976 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2722 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2718 theta)
    · exact b4_406 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1029 theta)
    · exact b4_4 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1027 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2791 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_21 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1168 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2973 theta)
    · exact b4_404 theta
theorem b3_3391 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3391 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_3391 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b3_3392 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3392 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(3,true)),(false,(0,true),(4,true))] s3_3392 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w24 rfl))))))))) (by decide +kernel)
theorem b3_3393 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3393 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(6,true),(1,true))] s3_3393 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons pc30w92 rfl)))))))))) (by decide +kernel)
theorem b3_3394 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3394 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(0,false),(1,true))] s3_3394 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffaaffaaffffffffffaaffaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons pc30w93 rfl)))))))))) (by decide +kernel)
theorem b3_3395 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3395 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(6,true),(3,true))] s3_3395 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons pc30w95 rfl)))))))))) (by decide +kernel)
theorem b3_3396 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3396 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,false),(3,true))] s3_3396 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000,0xfffffffffff0fff0fffffffffff0fff0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons pc30w96 rfl)))))))))) (by decide +kernel)
theorem b3_3397 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3397 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(6,true),(3,true))] s3_3397 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w98 (PetersenWireProjection.cons pc30w95 rfl)))))))))) (by decide +kernel)
theorem b3_3398 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3398 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_3398 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xfafafafafafafafafafafafafafafafa,0xfafafafafafafafafafafafafafafafa,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w103 (PetersenWireProjection.cons pc32w101 (PetersenWireProjection.cons pc32w100 rfl)))))))))) (by decide +kernel)
theorem b3_3399 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3399 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_3399 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w111 (PetersenWireProjection.cons pc34w107 (PetersenWireProjection.cons pc34w104 rfl)))))))))) (by decide +kernel)
theorem b3_3400 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3400 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_3400 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w76 (PetersenWireProjection.cons pc41w116 (PetersenWireProjection.cons pc41w73 rfl)))))))))) (by decide +kernel)
theorem b3_3401 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3401 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_3401 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w76 (PetersenWireProjection.cons pc41w117 (PetersenWireProjection.cons pc41w73 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
