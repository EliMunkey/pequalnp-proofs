import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S5
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S67
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S73
import Q1020K12L4S74
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc0w3 : PetersenPackedPin.project cycle0 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored50 stored54 rfl rfl

private theorem pc0w5 : PetersenPackedPin.project cycle0 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored51 stored54 rfl rfl
private theorem pc0w2 : PetersenPackedPin.project cycle0 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 0 pc0w3 pc0w5 rfl rfl
private theorem pc0w7 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl




private theorem pc0w12 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl



private theorem pc1w16 : PetersenPackedPin.project cycle1 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored62 rfl rfl

private theorem pc1w18 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored62 rfl rfl
private theorem pc1w15 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w16 pc1w18 rfl rfl




private theorem pc1w24 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl




private theorem pc30w27 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl



private theorem pc30w33 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored12 stored13 rfl rfl

private theorem pc30w35 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w36 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w37 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w38 : PetersenPackedPin.project extra30 (0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w27 stored13 rfl rfl
private theorem pc30w39 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w40 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w41 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w35 stored13 rfl rfl
private theorem pc30w42 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 3 pc30w35 stored13 rfl rfl




private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl




private theorem pc26w50 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc30w54 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w55 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w56 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w57 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w58 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl




private theorem pc32w61 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl


private theorem pc32w66 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored27 stored28 rfl rfl


private theorem pc32w69 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w70 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored26 stored28 rfl rfl
private theorem pc32w71 : PetersenPackedPin.project extra32 (0xff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w61 stored28 rfl rfl
private theorem pc32w72 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored25 stored28 rfl rfl
private theorem pc32w73 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w74 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0033003300330033003300330033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc32w69 stored28 rfl rfl
private theorem pc32w75 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ffccffccffccffccffccffccffccffcc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 3 pc32w69 stored28 rfl rfl
private theorem pc26w76 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl
private theorem pc30w77 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl




private theorem pc34w80 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl

private theorem pc34w84 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored18 stored19 rfl rfl



private theorem pc34w88 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w89 : PetersenPackedPin.project extra34 (0xffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w80 stored19 rfl rfl
private theorem pc34w90 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored17 stored19 rfl rfl
private theorem pc34w91 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored16 stored19 rfl rfl
private theorem pc34w92 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc34w88 stored19 rfl rfl
private theorem pc34w93 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w88 stored19 rfl rfl
private theorem pc26w94 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl
private theorem pc34w95 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl
private theorem pc34w96 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w97 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w98 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w99 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc30w100 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc32w101 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl
theorem b3_1050 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1050 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s3_1050 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0xcccccccc,0x0,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w12 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w7 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w2 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1051 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1051 := by
  apply PetersenIndexedNode.close (bank := [s4_414,a4257,a4258,s4_2492,a4259,s4_2764,s4_701,a4260,s4_300,a4261,a4262,s4_493,s4_233,a4263,a4264,s4_724,a4265,a4266,s4_727,s4_516,s4_214,a4267,a4268,s4_529,s4_165,a4269,a4270,a4271,s4_117,a4272,a4273,a4274,s4_726,s4_578,s4_811,s4_568,s4_812,s4_561,s4_814,a4275,s4_650]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108090808c282420231111850484444202108088404840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c04a0201080a80010808a0805000280814100a020420208404420270341080884048404614521011c0d0c28a4222210108404420226221080884040c0425051280898884a0a21050301084044202901028202400108089080480024041210090104202141010808501048401400084045040280014040a0805010210124200840416122820058080c045444030105848a88806120301141000c04311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a08084040e0a1410038080c042c240301038285848060a03010a0800c04280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a080504100288013a0c060040838141c0a1012000c8404210120e04840448086160120208404c2c021011202107024808030120e040c0484808012a12000c05002603012120107028480150520e04541421018011884045415002415050840507022101494120e05250050408010941012505002248411410107025040151120e045444282045c48a08054448b8915110a08107022820428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030242c080c08060406021292018090b02252410920180806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030241c0884804240c2c0018100c0907020302018130b004240212080104007d242484048002210108405001d2101120220038480821014007884044808800d920200c050019030121202003084800301400680c048480800ba1200541500151505084060028210115054005854142101800988406001f000e80069410200185040800940046002050408005941005445000915110a082001028201511400285444282080038a082000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_414 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_350 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2408 theta)
    · exact b4_2492 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_8 theta)
    · exact b4_2764 theta
    · exact b4_701 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_444 theta)
    · exact b4_300 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2392 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2523 theta)
    · exact b4_493 theta
    · exact b4_233 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2287 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2284 theta)
    · exact b4_724 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_3176 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2551 theta)
    · exact b4_727 theta
    · exact b4_516 theta
    · exact b4_214 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2700 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2827 theta)
    · exact b4_529 theta
    · exact b4_165 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2658 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_3110 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_539 theta)
    · exact b4_117 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2646 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2816 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3120 theta)
    · exact b4_726 theta
    · exact b4_578 theta
    · exact b4_811 theta
    · exact b4_568 theta
    · exact b4_812 theta
    · exact b4_561 theta
    · exact b4_814 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_650 theta)
    · exact b4_650 theta
theorem b3_1052 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1052 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1052 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w24 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w15 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1053 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1053 := by
  apply PetersenIndexedNode.close (bank := [a4276,s4_2493,a4277,s4_702,s4_301,a4278,s4_728,s4_732,s4_517,a4279,a4280,s4_730,s4_693,s4_670,s4_622,s4_750,s4_580,s4_758,s4_565,s4_778,s4_698,a4201,s4_628,s4_731]) (PetersenIndexedNode.reasons 256 17 420 0x622210808840484046141210118888c2824222210108404420251100a829400084045040280014440a0805110210105414840431110a828c4044202706010808c444e0c0211110808541442024808141012000840448402400120209080480821010a0808404280824200a0004202282014000a0205040280810809210042021d0d1410074142a0a38300a82874347060150d0a828a0802a0a46060a081180884046460210111818c8c04206210105040840424040a0809000420224201200090104840240410808504042021505121005404a08014100a80854142820150528200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0442026260108089818c4c02406108080c040602800b018080c042a0a13110980a002e262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406025110400550602840441c0a0c054440838150102101200288404210120e04840448086160120208404c2c021011202107024808150520e044202a080800908404541500131505282010702a080383020e04e0c05040800814100e0c1001138301410107025040141020e045040484045c49210050408b8914101210107024840030120e040c0484808007212000c05000f03012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030250c080c0806042a0a109008c094302212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0c00350700c2c0018100c0907020302018130b020018c2c08005c00292424840413122101084042624210112020c4c0480821011898084044808131212020541500091505282004c4826241505098905014a08080040a02a000c26241312141006c68362480038d8d04c6850401312098905444262415100a082000828201511400145044282013120a0800c0462600301212004c4826200301098900c048480313018982000700020180a0e044c48030101810989006042120800008480060500010181084804c482120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_345 theta)
    · exact b4_2493 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2650 theta)
    · exact b4_702 theta
    · exact b4_301 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2518 theta)
    · exact b4_728 theta
    · exact b4_732 theta
    · exact b4_517 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2695 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2929 theta)
    · exact b4_730 theta
    · exact b4_693 theta
    · exact b4_670 theta
    · exact b4_622 theta
    · exact b4_750 theta
    · exact b4_580 theta
    · exact b4_758 theta
    · exact b4_565 theta
    · exact b4_778 theta
    · exact b4_698 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_646 theta)
    · exact b4_628 theta
    · exact b4_731 theta
theorem b3_1054 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1054 := by
  apply PetersenIndexedNode.close (bank := [a4281,s4_703,s4_302,a4282,s4_234,s4_733,a4283,a4284,s4_737,a4285,a4286,a4287,s4_735,s4_623,s4_751,s4_581,s4_759,s4_569,s4_780,s4_698,a4201,s4_632,s4_736]) (PetersenIndexedNode.reasons 256 17 420 0x612010808840484046141210118480c28261202101084044202501008405400084045040280014040a080501021010420221013111084044202420230a090808c4446141211110808420221014808141012000840448402400120209080480821010a0808404290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840425050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c040602800a818080c04420262601080a002cc4c04260108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406026120400510602840441c0a0c058480838161202101200268404210120e048404c8886160120208404c2c021013222107028381150520e04541421018008884045415001215050840507022101282020e04a08090808007a4200a081001028202420107029080151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808006a12000c05000e03012120107028480428280c080604840441c1210110a0a83824202a10100604030264c480c080604420230b0108099312616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b004240212080064002d242484042120210108405000a210130a08848042402101109008404c28280049202854144240150508404c4c0210115051898054142101212008406000a42402120141020008504080044001e000c50402120109005444424015110a0820004282015114000c5444282021200a0800c0442400301212008c8846400301119100c048480212010902000300000180a0e04848003010181109000604212021a0884800604434101810848084802120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) (b4_2651 theta)
    · exact b4_703 theta
    · exact b4_302 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2517 theta)
    · exact b4_234 theta
    · exact b4_733 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3102 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2547 theta)
    · exact b4_737 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_534 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2641 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2932 theta)
    · exact b4_735 theta
    · exact b4_623 theta
    · exact b4_751 theta
    · exact b4_581 theta
    · exact b4_759 theta
    · exact b4_569 theta
    · exact b4_780 theta
    · exact b4_698 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_646 theta)
    · exact b4_632 theta
    · exact b4_736 theta
theorem b3_1055 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1055 := by
  apply PetersenIndexedNode.close (bank := [a4288,s4_2494,a4289,s4_740,s4_485,a4290,s4_303,a4291,s4_742,s4_745,s4_518,a4292,s4_120,a4293,a4294,s4_744,s4_624,s4_752,s4_582,s4_760,s4_565,s4_778,s4_739,a4295]) (PetersenIndexedNode.reasons 256 17 420 0x622210808840484046141210118888c2824222210108404420250100a828541484045041210114040a0825010210105414840431110a828c202420230a098404c4446141211110808541442024808141012000840448402400120209080480821010a0808404280824200a0004202282014000a0205040280810809210042021d0d1410074142a0a38300a82874347060150d0a828a0802a0a46060a081180884046460210111818c8c04206210105040840424040a0809000420224201200090104840240410808504042021505121005404614114100a80854142820150518504908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0442026260108089818c4c02406108080c04060232a2818080c042a0a131109808ca8a262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060250104005d0602840441c0a0c0540408381501021012002c8404210120e04840448086160120208404c2c021011202107024808150520e0442026141800a084045415001515051850507026141494120e05250050408009141012505001348411410107025040141020e045040484045c49210050408b8914101210107024840030120e040c0484808008212000c05001103012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c098580c2c0c2c0018100c0907020302018130b00c2c061608007c0039242484041312210108404262421011202200184808210140034840448081312120205415000b1505185044c4826241505098905014614180050a02a001026241312141006c68362480048d8d04c6850401312098905444262415100a082000c282015114001c5044282013120a0800c0500050301212004c4826200301098900c048480800221202000700020180a0e044c48030101810989006042120800008480060500010181084804c482120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_346 theta)
    · exact b4_2494 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2637 theta)
    · exact b4_740 theta
    · exact b4_485 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2315 theta)
    · exact b4_303 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2519 theta)
    · exact b4_742 theta
    · exact b4_745 theta
    · exact b4_518 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2696 theta)
    · exact b4_120 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2814 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2944 theta)
    · exact b4_744 theta
    · exact b4_624 theta
    · exact b4_752 theta
    · exact b4_582 theta
    · exact b4_760 theta
    · exact b4_565 theta
    · exact b4_778 theta
    · exact b4_739 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_524 theta)
theorem b3_1056 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1056 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1056 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w33 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1057 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1057 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1057 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w36 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1058 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1058 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1058 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1059 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1059 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1059 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w38 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1060 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1060 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1060 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w39 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1061 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1061 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1061 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1062 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1062 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1062 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w41 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1063 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1063 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1063 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff0000000000ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w42 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1064 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1064 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1064 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1065 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1065 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,false),(3,false))] s3_1065 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w55 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w54 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1066 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1066 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(3,true))] s3_1066 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w55 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w56 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1067 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1067 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(6,true))] s3_1067 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w55 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w57 rfl)))))))))) (by decide +kernel)
theorem b3_1068 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1068 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(3,true),(6,true))] s3_1068 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w55 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w58 rfl)))))))))) (by decide +kernel)
theorem b3_1069 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1069 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1069 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w66 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1070 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1070 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1070 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1071 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1071 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1071 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w71 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1072 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1072 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1072 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w72 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1073 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1073 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1073 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1074 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1074 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1074 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w74 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1075 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1075 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1075 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w75 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1076 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1076 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1076 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1077 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1077 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1077 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1078 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1078 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1078 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w84 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1079 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1079 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1079 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1080 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1080 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1080 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w90 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1081 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1081 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1081 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1082 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1082 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1082 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w92 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1083 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1083 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1083 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w92 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1084 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1084 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1084 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w93 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1085 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1085 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1085 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w94 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1086 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1086 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,false),(5,false))] s3_1086 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f00000f0f00000f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w96 (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1087 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1087 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(5,true))] s3_1087 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w96 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w97 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1088 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1088 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(7,true))] s3_1088 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w96 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w98 rfl)))))))))) (by decide +kernel)
theorem b3_1089 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1089 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(5,true),(7,true))] s3_1089 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w96 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w99 rfl)))))))))) (by decide +kernel)
theorem b3_1090 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1090 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1090 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w35 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w100 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1091 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1091 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1091 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w69 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w101 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
