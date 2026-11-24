import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S12
import Q1020K12L3S13
import Q1020K12L3S14
import Q1020K12L3S15
import Q1020K12L3S16
import Q1020K12L3S17
import Q1020K12L3S18
import Q1020K12L3S19
import Q1020K12L3S20
import Q1020K12L3S21
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S24
import Q1020K12L3S25
import Q1020K12L3S26
import Q1020K12L3S27
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S62
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S71
import Q1020K12L3S72
import Q1020K12L3S73
import Q1020K12L3S77
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
import Q1020K12L3S81
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc30w3 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl



private theorem pc30w9 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl





private theorem pc32w13 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl



private theorem pc32w19 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl



private theorem pc1w23 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl





private theorem pc1w29 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl




private theorem pc3w34 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w33 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff0000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc3w34 stored35 rfl rfl




private theorem pc3w40 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w34 stored35 rfl rfl




private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl




private theorem pc26w50 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc3w51 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc30w52 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc32w53 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl




private theorem pc34w56 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl




private theorem pc34w63 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc1w64 : PetersenPackedPin.project cycle1 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored58 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xffffffffffffffff000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc3w34 stored34 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w34 stored34 rfl rfl
private theorem pc26w67 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc30w69 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w70 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w71 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc30w74 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc32w75 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w34 stored36 rfl rfl
private theorem pc30w78 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc34w79 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc30w80 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc30w82 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w82 stored8 rfl rfl
private theorem pc30w83 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc30w84 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w85 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x55555555000000005555555500000000 := PetersenWireProjection.derive 1 stored8 stored10 rfl rfl
private theorem pc30w86 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w87 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff0000000000 := PetersenWireProjection.derive 0 stored8 stored14 rfl rfl
theorem b2_168 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_168 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_168 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w3 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_169 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_169 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_169 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w19 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w13 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_170 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_170 := by
  apply PetersenIndexedNode.close (bank := [s3_386,a995,a996,s3_2715,a997,a998,s3_850,s3_533,a999,a1000,a1001,a1002,s3_333,a1003,a1004,s3_546,s3_294,a1005,a1006,s3_904,a1007,a1008,s3_1033,s3_558,a1009,s3_554,s3_277,s3_276,s3_275,a1010,a1011,s3_917,a1012,a1013,s3_922,s3_570,s3_256,a1014,a1015,a1016,s3_119,a1017,a1018,a1019,s3_919,s3_825,s3_690,s3_808,s3_939,s3_767,s3_1065,s3_728,s3_1086,s3_845,s3_700,s3_699,s3_698,a1020,s3_1100,s3_1092,s3_940,s3_691,s3_1093,a1021,s3_793,s3_870,s3_703,s3_702,s3_701,s3_773,s3_1051,s3_1050,s3_946,s3_883,s3_705,s3_752,s3_947,s3_897,s3_706,s3_734,s3_948,s3_2,s3_672,a933,s3_711,a985,s3_916,a843,s3_726,s3_991,s3_921,s3_920]) (PetersenIndexedNode.reasons 256 17 510 0x18888420221012101185048404622230a0908888404210110809404021015000210114100a0005010282014040840410808840600aa210110809080a00a64202802dc01688444e060802c381810809005742023818200b2e06042024015908090055802a188888405005121014014e00a461411080c01444202901028202400108089080480024041210090104202141010808501048401400084045040280014040a08050102101242008404311128200c4044202706010808c444e0c021111080941004203004f282014102009c7060383040140e0c07060802694100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a0808404280824200a0004202282014000a020504028081080921004203004b14100a08200946860343040130d0c0686080248a0805040988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c042505030109404420226221080894144c4421051080818084203004503010180a00890043802140122008f00468020818080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c050040801fa0c060058838141c0a1012000c8404210120e04840448086160120208404c2c021011202107024808150520e0454142101801e884045415003e15050840507022101801ca0e0507030038801bc00da0079003b801d400d507028381494120e05250050408019941012505003448411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808018a12000c05003203012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b0108089212616024049080806040302108080c08420028081090084004202212010808a02006040302801780c080605002e30b0185820060616030b0400b40604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208016400ad2424840480022101084050029210112022005048082101400a884044808801392020541500251505084060048210115054009854142101801188406003f001e800ec00720037001a80114008600410019800c4005e0027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_386 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_356 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2630 theta)
    · exact b3_2715 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_9 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2783 theta)
    · exact b3_850 theta
    · exact b3_533 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_318 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2439 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2736 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_414 theta)
    · exact b3_333 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2620 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2726 theta)
    · exact b3_546 theta
    · exact b3_294 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2421 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2417 theta)
    · exact b3_904 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2833 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2740 theta)
    · exact b3_1033 theta
    · exact b3_558 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_556 theta)
    · exact b3_554 theta
    · exact b3_277 theta
    · exact b3_276 theta
    · exact b3_275 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2764 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2763 theta)
    · exact b3_917 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2857 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2770 theta)
    · exact b3_922 theta
    · exact b3_570 theta
    · exact b3_256 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2771 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2777 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_597 theta)
    · exact b3_119 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2772 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2775 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2803 theta)
    · exact b3_919 theta
    · exact b3_825 theta
    · exact b3_690 theta
    · exact b3_808 theta
    · exact b3_939 theta
    · exact b3_767 theta
    · exact b3_1065 theta
    · exact b3_728 theta
    · exact b3_1086 theta
    · exact b3_845 theta
    · exact b3_700 theta
    · exact b3_699 theta
    · exact b3_698 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_565 theta)
    · exact b3_1100 theta
    · exact b3_1092 theta
    · exact b3_940 theta
    · exact b3_691 theta
    · exact b3_1093 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_793 theta)
    · exact b3_793 theta
    · exact b3_870 theta
    · exact b3_703 theta
    · exact b3_702 theta
    · exact b3_701 theta
    · exact b3_773 theta
    · exact b3_1051 theta
    · exact b3_1050 theta
    · exact b3_946 theta
    · exact b3_883 theta
    · exact b3_705 theta
    · exact b3_752 theta
    · exact b3_947 theta
    · exact b3_897 theta
    · exact b3_706 theta
    · exact b3_734 theta
    · exact b3_948 theta
    · exact b3_2 theta
    · exact b3_672 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_670 theta)
    · exact b3_711 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_710 theta)
    · exact b3_916 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_562 theta)
    · exact b3_726 theta
    · exact b3_991 theta
    · exact b3_921 theta
    · exact b3_920 theta
theorem b2_171 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_171 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_171 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w29 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w23 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b2_172 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_172 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_172 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_173 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_173 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_173 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w40 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_174 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_174 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_174 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_175 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_175 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_175 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w51 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_176 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_176 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_176 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w52 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_177 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_177 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_177 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w19 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w53 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_178 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_178 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_178 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w56 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_179 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_179 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_179 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w29 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w64 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b2_180 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_180 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_180 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_181 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_181 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_181 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_182 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_182 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_182 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_183 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_183 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_183 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w68 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_184 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_184 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_184 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w69 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_185 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_185 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_185 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w19 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_186 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_186 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_186 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w71 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_187 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_187 := by
  apply PetersenIndexedNode.close (bank := [s3_387,a1022,a1023,s3_2716,a1024,a1025,s3_851,s3_534,a1026,a1027,a1028,a1029,s3_334,a1030,a1031,s3_547,s3_295,a1032,a1033,s3_905,s3_3421,a1034,s3_1034,s3_573,s3_263,a1035,a1036,s3_927,a1037,a1038,s3_1025,a1039,s3_128,a1040,a1041,s3_613,s3_612,s3_610,s3_32,s3_31,s3_29,a1042,a1043,s3_970,a1044,a1045,s3_975,a1046,s3_974,s3_815,s3_1019,s3_833,a1047,s3_817,s3_976,s3_768,s3_1066,s3_729,s3_1087,s3_693,a1048,s3_1138,s3_1122,s3_1028,s3_849,a1049,s3_792,s3_977,a1050,s3_796,s3_873,a1051,s3_781,s3_978,s3_753,s3_1030,s3_756,s3_1021,s3_888,s3_887,s3_886,a1052,s3_760,s3_759,s3_758,s3_979,s3_735,s3_1031,s3_901,a1053,s3_742,s3_980,s3_921,s3_920,a934,a984,s3_2,s3_711,s3_672,s3_658,s3_1024,s3_969,s3_661,a1054,s3_1004]) (PetersenIndexedNode.reasons 256 17 510 0x14041006750102101200cc84045010401a1404084048032a10118888622270102101200c684046222401918888840431112101200c5005e210140180c4444202501018505404084047060210114040e0c0501021010c28284048030c017c4203006030a088404c445005f311140178c2826141802ec01708444901028202400108089080480024041210090104202141010809005a48402420200b2504028204016ca0805040802c242012100703048401c080c444504038101c0c0a0807030311124200c4450056282014100c282706038204015ce0c0506030a094100a0808c0c1410230110808c8c04202230319180840c42020a081080900548029c014a00a228201410401545040282080284013e009d004c14100a080c44448403410401349080484031110a0805041004a242012100c282282014104012c5040282030a0921009080988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c05004803010180a008e26221311401244c4426228023018080c047434030101808c444c4c031111d0d1898070343111018080c046545030101808c28226221311195144c44262230a0818080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c050045802220c060060838141c0a1012000c8404802120e0507030041616030b020086c2c061604010107028381311120e04c444703061601c0c0c444c2c031111c0c107027030801e20e0507026141801d98506007f003e801e9850507026141494120e0525005040801c941012505003a48411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c048480801ba12000c05003803012120107028480428280c080604840441c1210110a0a83824202a101006040302801a80c0806050034109008482006c21201090400cc06040302801880c080604622230b0184820064616010b0188880604030230a080c080604e0c0109008480c28221201090383000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208018400bd242484048002210120057002a8014c00a2004f00268017400b60059002580124008cc445002131111c0c200407030311140088c4447030800f9c0c20037001a800c9850600306141800f4007600386141800b985060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_387 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_357 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2632 theta)
    · exact b3_2716 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_18 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2803 theta)
    · exact b3_851 theta
    · exact b3_534 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_319 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2442 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2739 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_415 theta)
    · exact b3_334 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2621 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2727 theta)
    · exact b3_547 theta
    · exact b3_295 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2424 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2420 theta)
    · exact b3_905 theta
    · exact b3_3421 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2742 theta)
    · exact b3_1034 theta
    · exact b3_573 theta
    · exact b3_263 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2921 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2915 theta)
    · exact b3_927 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3367 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3098 theta)
    · exact b3_1025 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_599 theta)
    · exact b3_128 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2854 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3046 theta)
    · exact b3_613 theta
    · exact b3_612 theta
    · exact b3_610 theta
    · exact b3_32 theta
    · exact b3_31 theta
    · exact b3_29 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2966 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2965 theta)
    · exact b3_970 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3305 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3269 theta)
    · exact b3_975 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3290 theta)
    · exact b3_974 theta
    · exact b3_815 theta
    · exact b3_1019 theta
    · exact b3_833 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_159 theta)
    · exact b3_817 theta
    · exact b3_976 theta
    · exact b3_768 theta
    · exact b3_1066 theta
    · exact b3_729 theta
    · exact b3_1087 theta
    · exact b3_693 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_685 theta)
    · exact b3_1138 theta
    · exact b3_1122 theta
    · exact b3_1028 theta
    · exact b3_849 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_86 theta)
    · exact b3_792 theta
    · exact b3_977 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_796 theta)
    · exact b3_796 theta
    · exact b3_873 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_48 theta)
    · exact b3_781 theta
    · exact b3_978 theta
    · exact b3_753 theta
    · exact b3_1030 theta
    · exact b3_756 theta
    · exact b3_1021 theta
    · exact b3_888 theta
    · exact b3_887 theta
    · exact b3_886 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_183 theta)
    · exact b3_760 theta
    · exact b3_759 theta
    · exact b3_758 theta
    · exact b3_979 theta
    · exact b3_735 theta
    · exact b3_1031 theta
    · exact b3_901 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_164 theta)
    · exact b3_742 theta
    · exact b3_980 theta
    · exact b3_921 theta
    · exact b3_920 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_673 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_712 theta)
    · exact b3_2 theta
    · exact b3_711 theta
    · exact b3_672 theta
    · exact b3_658 theta
    · exact b3_1024 theta
    · exact b3_969 theta
    · exact b3_661 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_101 theta)
    · exact b3_1004 theta
theorem b2_188 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_188 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_188 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b2_189 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_189 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_189 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w72 rfl)))))))))) (by decide +kernel)
theorem b2_190 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_190 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_190 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w73 rfl)))))))))) (by decide +kernel)
theorem b2_191 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_191 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_191 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w74 rfl)))))))))) (by decide +kernel)
theorem b2_192 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_192 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_192 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w19 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w75 rfl)))))))))) (by decide +kernel)
theorem b2_193 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_193 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_193 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w76 rfl)))))))))) (by decide +kernel)
theorem b2_194 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_194 := by
  apply PetersenIndexedNode.close (bank := [s3_388,a1055,a1056,s3_2717,a784,a1057,s3_852,s3_535,a1058,a1059,a1060,a1061,s3_335,a1062,a1063,s3_548,s3_296,a1064,a1065,s3_906,s3_3426,a1066,s3_1036,s3_579,s3_265,a1067,a1068,s3_928,a801,a802,s3_1026,s3_604,s3_133,a1069,a1070,a1071,s3_1011,s3_574,s3_559,s3_264,s3_232,a1072,a1073,s3_986,a807,a808,s3_994,s3_818,s3_1007,s3_838,s3_205,s3_820,s3_993,s3_769,s3_1067,s3_730,s3_1088,s3_695,s3_1130,a1074,s3_797,s3_859,s3_860,s3_858,s3_800,s3_801,s3_799,s3_774,s3_1029,s3_877,a1075,s3_786,s3_995,s3_761,s3_1015,s3_891,a1076,s3_764,s3_996,s3_736,s3_1032,s3_908,a1077,s3_745,s3_997,s3_925,s3_924,s3_634,s3_721,s3_2,s3_720,s3_956,a881,s3_688,s3_1004,s3_632]) (PetersenIndexedNode.reasons 256 17 510 0x200bf005742024016540408404802e908088405005c31111888a00bc622231114016c840442027030108088404a020614128081c0c0c28250302808084044202802d40160420300595040084054041005850104015d4100a080802b40155084862225040188888404e0c0210118889c18062222101282008405005328201410200a47060383040150e0c07060802894100a080b03028202c0814040908050102c0c12100a0305010141014040501048401400084045040280014040a08050102101242008405004f28201410141007060383040140e0c07060504014100a081004d24201210200982820141040138504028208025921009081004914100a0814040c8c05010401299180c8c050100a08050404808141012000840448402400120209080480821010a0808404a8882420121014100282014102a220504028205040121009080988814100a080a08038301c10262207060283028200a0805041004703010180a008c26221311401204c4426228022818080c04a424030101809404084805010290910900a0245010018080c044c0c0301018088404c4c02101130318980480c2101018080c050043030101809410026221311401104c4426225040018080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0500428020c01020050838141c0c00b907028381801fc00fa007b003c801da88820048838141c0a8082000ca020210120e04840448086160120208404c2c021011202107024808514120e054500a080801ca82014505003a5041282010702a080494120e0525005040801b941012505003848411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c048480801aa12000c05003603012120107028480801980c0806050032109008482006821201090400c406040302801780c080604a02041c1280820060838241c12808006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208015c00aa00530028800c4009e005d002d80164009a002f002580124008d4444a020800228080840500212101120220040480821014008884044808800f920220037001a800ca82020030a080800f400760038a080800ba82020027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_388 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_359 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2631 theta)
    · exact b3_2717 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_19 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2796 theta)
    · exact b3_852 theta
    · exact b3_535 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_321 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2440 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2738 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_417 theta)
    · exact b3_335 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2622 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2729 theta)
    · exact b3_548 theta
    · exact b3_296 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2423 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2419 theta)
    · exact b3_906 theta
    · exact b3_3426 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2743 theta)
    · exact b3_1036 theta
    · exact b3_579 theta
    · exact b3_265 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2922 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2917 theta)
    · exact b3_928 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3366 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3090 theta)
    · exact b3_1026 theta
    · exact b3_604 theta
    · exact b3_133 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2853 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3063 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_3273 theta)
    · exact b3_1011 theta
    · exact b3_574 theta
    · exact b3_559 theta
    · exact b3_264 theta
    · exact b3_232 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_3057 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3052 theta)
    · exact b3_986 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3330 theta)
    · exact b3_994 theta
    · exact b3_818 theta
    · exact b3_1007 theta
    · exact b3_838 theta
    · exact b3_205 theta
    · exact b3_820 theta
    · exact b3_993 theta
    · exact b3_769 theta
    · exact b3_1067 theta
    · exact b3_730 theta
    · exact b3_1088 theta
    · exact b3_695 theta
    · exact b3_1130 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_795 theta)
    · exact b3_797 theta
    · exact b3_859 theta
    · exact b3_860 theta
    · exact b3_858 theta
    · exact b3_800 theta
    · exact b3_801 theta
    · exact b3_799 theta
    · exact b3_774 theta
    · exact b3_1029 theta
    · exact b3_877 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_209 theta)
    · exact b3_786 theta
    · exact b3_995 theta
    · exact b3_761 theta
    · exact b3_1015 theta
    · exact b3_891 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_206 theta)
    · exact b3_764 theta
    · exact b3_996 theta
    · exact b3_736 theta
    · exact b3_1032 theta
    · exact b3_908 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_210 theta)
    · exact b3_745 theta
    · exact b3_997 theta
    · exact b3_925 theta
    · exact b3_924 theta
    · exact b3_634 theta
    · exact b3_721 theta
    · exact b3_2 theta
    · exact b3_720 theta
    · exact b3_956 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_237 theta)
    · exact b3_688 theta
    · exact b3_1004 theta
    · exact b3_632 theta
theorem b2_195 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_195 := by
  apply PetersenIndexedNode.close (bank := [s3_389,a1078,a1079,s3_2718,a764,a1080,s3_853,s3_536,a1081,a1082,a1083,a1084,s3_336,a1085,a1086,s3_549,s3_297,a1087,a1088,s3_907,s3_3427,a1089,s3_1037,s3_580,a1090,a1091,a1092,a1093,s3_134,a1094,a1095,s3_953,a777,a778,s3_1018,s3_3402,a1096,s3_1013,s3_600,s3_591,s3_129,s3_74,a1097,a1098,s3_987,a780,a781,s3_1000,s3_839,s3_46,s3_821,s3_999,s3_770,s3_1068,s3_731,s3_1089,a1099,s3_1132,a1100,s3_798,s3_862,s3_863,s3_861,s3_803,s3_804,s3_802,s3_779,s3_1020,s3_878,s3_155,s3_787,s3_1001,s3_762,s3_1016,s3_892,a1101,s3_765,s3_1002,s3_740,s3_1022,s3_743,s3_1017,s3_910,s3_911,s3_909,s3_181,s3_747,s3_748,s3_746,s3_1003,s3_715,s3_1024,s3_931,a844,s3_725,s3_1004,s3_951,s3_950,a883,s3_684,s3_2,s3_683,s3_653]) (PetersenIndexedNode.reasons 256 17 510 0x200cd0062420240191888884048032c018c84050064614110809888900636222401898504c2828030c01810889005e10808840600ba614130a0c017cc2826141802e084044202e0601080884058888a0807020381814100e0606222084044203005a1080884058504614130a0c016cc282614161410840442030058802bc015a00aa5040282040164a0805040802a4014e00a500502820141018888908068204014521009080622214100a081004e4840242018504504028204013ca08050406141242012100311128200c4044202706010808c444e0c021111080941004203004c14100a082009648402420401349080484080250a0805041004814100a0818888c8c0642040125918048c062220a0805040c88814100a081850448402420322209080484061410a0805040280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805041004603010180a008a848042404011d090084808022018080c04c444030101809c0c084806220311110900c4447030018080c0500420301018098504c4c062404010d898084c06141018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0500418020400fe0052838141c0c00bd07028381801f400f60079003b801d30902004a838141c0b1112000cc444614120e058500c888616030a018504c2c061413222107028381150520e0454142101801c084045415003915050840507022101494120e0525005040801b141012505003748411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c048480801a212000c05003503012120107028480801900c080605003130b0185820066616030b0400c00604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208016400ae00550029800e400a2005f002e8016c009e003700268012c00920046c444800231112003f001e800eb0a0a0038c2828011400860040c282800db0a08541500191505084060030210115054006854142101800b884060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_389 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_358 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2633 theta)
    · exact b3_2718 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_18 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2800 theta)
    · exact b3_853 theta
    · exact b3_536 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_320 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2441 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2737 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_416 theta)
    · exact b3_336 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2623 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2728 theta)
    · exact b3_549 theta
    · exact b3_297 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2422 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2418 theta)
    · exact b3_907 theta
    · exact b3_3427 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2741 theta)
    · exact b3_1037 theta
    · exact b3_580 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_263 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2918 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3104 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_603 theta)
    · exact b3_134 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2856 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2852 theta)
    · exact b3_953 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3363 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3059 theta)
    · exact b3_1018 theta
    · exact b3_3402 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3278 theta)
    · exact b3_1013 theta
    · exact b3_600 theta
    · exact b3_591 theta
    · exact b3_129 theta
    · exact b3_74 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_3020 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_3009 theta)
    · exact b3_987 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3351 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3281 theta)
    · exact b3_1000 theta
    · exact b3_839 theta
    · exact b3_46 theta
    · exact b3_821 theta
    · exact b3_999 theta
    · exact b3_770 theta
    · exact b3_1068 theta
    · exact b3_731 theta
    · exact b3_1089 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_693 theta)
    · exact b3_1132 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_794 theta)
    · exact b3_798 theta
    · exact b3_862 theta
    · exact b3_863 theta
    · exact b3_861 theta
    · exact b3_803 theta
    · exact b3_804 theta
    · exact b3_802 theta
    · exact b3_779 theta
    · exact b3_1020 theta
    · exact b3_878 theta
    · exact b3_155 theta
    · exact b3_787 theta
    · exact b3_1001 theta
    · exact b3_762 theta
    · exact b3_1016 theta
    · exact b3_892 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_158 theta)
    · exact b3_765 theta
    · exact b3_1002 theta
    · exact b3_740 theta
    · exact b3_1022 theta
    · exact b3_743 theta
    · exact b3_1017 theta
    · exact b3_910 theta
    · exact b3_911 theta
    · exact b3_909 theta
    · exact b3_181 theta
    · exact b3_747 theta
    · exact b3_748 theta
    · exact b3_746 theta
    · exact b3_1003 theta
    · exact b3_715 theta
    · exact b3_1024 theta
    · exact b3_931 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_81 theta)
    · exact b3_725 theta
    · exact b3_1004 theta
    · exact b3_951 theta
    · exact b3_950 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_654 theta)
    · exact b3_684 theta
    · exact b3_2 theta
    · exact b3_683 theta
    · exact b3_653 theta
theorem b2_196 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_196 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_196 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w73 rfl))))))))) (by decide +kernel)
theorem b2_197 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_197 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_197 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w34 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w77 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b2_198 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_198 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_198 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w78 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b2_199 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_199 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_199 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w79 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_200 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_200 := by
  apply PetersenIndexedNode.close (bank := [s3_381,a1102,a1103,s3_837,s3_2719,s3_840,s3_528,a1104,s3_1062,s3_1063,a1105,s3_338,s3_328,s3_1074,a1106,s3_1075,s3_541,s3_289,s3_1083,s3_1082,s3_1139,s3_1084,s3_582,s3_560,s3_233,a1107,s3_1095,s3_1096,s3_3,a1108,s3_1104,s3_1103,s3_592,s3_75,s3_1115,s3_1116,a1109,s3_1133,s3_1126,s3_822,s3_766,s3_805,s3_1064,s3_823,s3_749,s3_806,s3_1076,s3_824,s3_727,s3_807,s3_1085,s3_826,s3_689,s3_810,s3_809,s3_1136,s3_1098,s3_830,s3_829,a1110,s3_814,s3_811,s3_1107,s3_831,a1111,s3_816,s3_1117,s3_834,s3_428,s3_819,s3_1125,s3_1056,s3_750,s3_771,s3_1077,s3_1057,s3_732,s3_772,s3_1090,s3_1058,a1112,s3_776,s3_775,s3_1137,s3_1108,s3_1059,a1113,s3_778,s3_777,s3_1134,s3_1109,s3_1060,a1114,s3_780,s3_1119,s3_1061,s3_615,s3_782,s3_1127,s3_1069,s3_733,s3_751,s3_1091,s3_1070,s3_704,s3_754,s3_1110,s3_1071,a1115,s3_755,s3_1111,s3_1072,s3_662,s3_757,s3_1120,s3_1073,a1116,s3_763,s3_1128,s3_1078,a1117,s3_737,s3_1112,s3_1079,a1118,s3_739,s3_738,s3_1135,s3_1113,s3_1080,s3_663,s3_741,s3_1121,s3_1081,s3_617,s3_744,s3_1129,a1119,s3_694,s3_692,s3_1093,s3_679,a940,a992,s3_1138,s3_1122,s3_1094,s3_642,s3_722,s3_1130,s3_1099,s3_682,a1120,s3_1123,s3_1102,s3_1101,s3_644,a1121,a1122,s3_1131,s3_1114,a887,s3_685,s3_1132]) (PetersenIndexedNode.reasons 256 17 552 0x805131110840442028050a1011850484048051b11118504844480502101084044202804f28082013a8301804e2101107028301804fa80810702a020804da101201348404804c1080907024202804b9202185804808804c9080985804202804b1202107024808804a2808054142a0a8049a101141048404804aa80814104a020804921010541484048047988885414620280471080a011a420280489888a01204222804610808541442028045c022a01122101800e20e04541421018043a4040a080900080432101121009000804424041210090108042a1010a080840480419404121005000804110808a0805000804214040a080501080409080921004202803f401f4a0805040803e20e04e0c070608040401fce0c07060803da0e04a0805040803c8e868a0803a0a803c0a828e0c02a0a803d0e868e0c02a1a803b8a828a0802a0a803aa303050408c04803a2101191808404803b230319180840c8039a101050408404803892020504048008038108089080480080391202090804808803790808504042028036a2e2490804840803620e0450402820803722e24504028208035a0e049080484080348a82890802a0280342820850402a0280350a82850402a0a8033a8208908048408032a6220504028208032141007060382080332622070602830803194100504028208030a10100c0484008030240410900840080312101109008404802fa40400c040602802e930300c040602802e1080989804202802f130318980480c802d908080c040602802c4015d09008480802b20e040c040602802d401640c040602802aa0e05090084808029401440c04060280280a8284c442602802a4014c4c44062280278a8280c0406028026951100c0406028026141002c2416028027151102c2406128025941000c04060280248b0900c04060280240a0801c140e0280250b0901c14060a80238a0800c0406028022a14140604030280222101107048404802321415070484058021a10100604030280209242406040302802010808c2c04202802112424c2c04809801f9080806040302801ea0e0600788380801db0b0006040302801f20e0406040302801d30b020072c2c0801b400d406040302801a0a82842402302801c400dc4240212080198a82806040302801894504060403028018141002624130280191450426240312801794100060403028016925040604030280160a08016140b028017125041614030a80158a080060403028014a1604060403028014018084a4806028015216044a4821248013818080604030280134009600489212800e210104c4884048011108084c484202801092020c4c04808801190808c4c042028010120204c484808800fc007a003a0301800e20e044c480301800d0a82a00322a0a800c282084c482624800d8a8284c48280a800ba820a002c280a8009c00484c4826248008941006c683624800ac00506c6826348008141004c48262480068a8884c482a2080060a0820016282080078a88a001c282280050a0804c482820800401808c4c006028003a12004c4826208004818084c480602800321200c4c06260800180c084c48030280010848200022120800280c0a000803028000084804c482120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_381 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_360 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_353 theta)
    · exact b3_837 theta
    · exact b3_2719 theta
    · exact b3_840 theta
    · exact b3_528 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_312 theta)
    · exact b3_1062 theta
    · exact b3_1063 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_411 theta)
    · exact b3_338 theta
    · exact b3_328 theta
    · exact b3_1074 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2730 theta)
    · exact b3_1075 theta
    · exact b3_541 theta
    · exact b3_289 theta
    · exact b3_1083 theta
    · exact b3_1082 theta
    · exact b3_1139 theta
    · exact b3_1084 theta
    · exact b3_582 theta
    · exact b3_560 theta
    · exact b3_233 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2920 theta)
    · exact b3_1095 theta
    · exact b3_1096 theta
    · exact b3_3 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_3030 theta)
    · exact b3_1104 theta
    · exact b3_1103 theta
    · exact b3_592 theta
    · exact b3_75 theta
    · exact b3_1115 theta
    · exact b3_1116 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_3402 theta)
    · exact b3_1133 theta
    · exact b3_1126 theta
    · exact b3_822 theta
    · exact b3_766 theta
    · exact b3_805 theta
    · exact b3_1064 theta
    · exact b3_823 theta
    · exact b3_749 theta
    · exact b3_806 theta
    · exact b3_1076 theta
    · exact b3_824 theta
    · exact b3_727 theta
    · exact b3_807 theta
    · exact b3_1085 theta
    · exact b3_826 theta
    · exact b3_689 theta
    · exact b3_810 theta
    · exact b3_809 theta
    · exact b3_1136 theta
    · exact b3_1098 theta
    · exact b3_830 theta
    · exact b3_829 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_184 theta)
    · exact b3_814 theta
    · exact b3_811 theta
    · exact b3_1107 theta
    · exact b3_831 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_433 theta)
    · exact b3_816 theta
    · exact b3_1117 theta
    · exact b3_834 theta
    · exact b3_428 theta
    · exact b3_819 theta
    · exact b3_1125 theta
    · exact b3_1056 theta
    · exact b3_750 theta
    · exact b3_771 theta
    · exact b3_1077 theta
    · exact b3_1057 theta
    · exact b3_732 theta
    · exact b3_772 theta
    · exact b3_1090 theta
    · exact b3_1058 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_437 theta)
    · exact b3_776 theta
    · exact b3_775 theta
    · exact b3_1137 theta
    · exact b3_1108 theta
    · exact b3_1059 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_165 theta)
    · exact b3_778 theta
    · exact b3_777 theta
    · exact b3_1134 theta
    · exact b3_1109 theta
    · exact b3_1060 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_450 theta)
    · exact b3_780 theta
    · exact b3_1119 theta
    · exact b3_1061 theta
    · exact b3_615 theta
    · exact b3_782 theta
    · exact b3_1127 theta
    · exact b3_1069 theta
    · exact b3_733 theta
    · exact b3_751 theta
    · exact b3_1091 theta
    · exact b3_1070 theta
    · exact b3_704 theta
    · exact b3_754 theta
    · exact b3_1110 theta
    · exact b3_1071 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_160 theta)
    · exact b3_755 theta
    · exact b3_1111 theta
    · exact b3_1072 theta
    · exact b3_662 theta
    · exact b3_757 theta
    · exact b3_1120 theta
    · exact b3_1073 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_430 theta)
    · exact b3_763 theta
    · exact b3_1128 theta
    · exact b3_1078 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_439 theta)
    · exact b3_737 theta
    · exact b3_1112 theta
    · exact b3_1079 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_49 theta)
    · exact b3_739 theta
    · exact b3_738 theta
    · exact b3_1135 theta
    · exact b3_1113 theta
    · exact b3_1080 theta
    · exact b3_663 theta
    · exact b3_741 theta
    · exact b3_1121 theta
    · exact b3_1081 theta
    · exact b3_617 theta
    · exact b3_744 theta
    · exact b3_1129 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_696 theta)
    · exact b3_694 theta
    · exact b3_692 theta
    · exact b3_1093 theta
    · exact b3_679 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_675 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_715 theta)
    · exact b3_1138 theta
    · exact b3_1122 theta
    · exact b3_1094 theta
    · exact b3_642 theta
    · exact b3_722 theta
    · exact b3_1130 theta
    · exact b3_1099 theta
    · exact b3_682 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_88 theta)
    · exact b3_1123 theta
    · exact b3_1102 theta
    · exact b3_1101 theta
    · exact b3_644 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_102 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_103 theta)
    · exact b3_1131 theta
    · exact b3_1114 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_658 theta)
    · exact b3_685 theta
    · exact b3_1132 theta
theorem b2_201 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_201 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s2_201 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_202 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_202 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s2_202 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b2_203 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_203 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s2_203 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_204 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_204 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true))] s2_204 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf000f000f000f000f000f000f000f00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons pc30w84 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_205 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_205 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(0,true))] s2_205 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x55555555000000005555555500000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_206 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_206 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,true))] s2_206 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf000f000f000f000f000f000f000f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_207 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_207 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_207 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w87 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_208 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_208 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false))] s2_208 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_209 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_209 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(3,false))] s2_209 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff0000000000ff00ff0000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w89 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
