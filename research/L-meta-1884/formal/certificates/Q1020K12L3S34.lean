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
import Q1020K12L4S6
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S24
import Q1020K12L4S54
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S74
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc26w0 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl

private theorem pc26w3 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl





private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl


private theorem pc2w12 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl

private theorem pc2w11 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w12 stored41 rfl rfl





private theorem pc2w21 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl


private theorem pc30w22 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl

private theorem pc30w25 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl





private theorem pc30w32 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc2w33 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored41 stored47 rfl rfl


private theorem pc41w35 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl

private theorem pc41w38 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl





private theorem pc41w45 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored90 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc2w48 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w47 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 pc2w48 stored41 rfl rfl
private theorem pc2w49 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc2w50 : PetersenPackedPin.project cycle2 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w21 stored42 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc30w53 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w54 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w55 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl


private theorem pc34w56 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl

private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl





private theorem pc34w66 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl


private theorem pc1w69 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl

private theorem pc1w68 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w69 stored58 rfl rfl





private theorem pc1w77 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 stored57 stored59 rfl rfl
private theorem pc2w78 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc2w81 : PetersenPackedPin.project cycle2 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored42 stored44 rfl rfl
private theorem pc2w82 : PetersenPackedPin.project cycle2 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored43 stored44 rfl rfl
private theorem pc2w80 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 2 pc2w81 pc2w82 rfl rfl
private theorem pc2w83 : PetersenPackedPin.project cycle2 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc2w12 stored44 rfl rfl
private theorem pc1w85 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl
private theorem pc1w86 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w84 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w85 pc1w86 rfl rfl
private theorem pc1w88 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored57 stored61 rfl rfl
private theorem pc1w89 : PetersenPackedPin.project cycle1 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored58 stored61 rfl rfl
private theorem pc1w87 : PetersenPackedPin.project cycle1 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 pc1w88 pc1w89 rfl rfl
private theorem pc2w91 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w90 : PetersenPackedPin.project cycle2 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w91 stored45 rfl rfl
private theorem pc1w93 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w92 : PetersenPackedPin.project cycle1 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc1w93 stored61 rfl rfl
private theorem pc1w95 : PetersenPackedPin.project cycle1 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored59 stored61 rfl rfl
private theorem pc1w94 : PetersenPackedPin.project cycle1 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 0 pc1w88 pc1w95 rfl rfl



private theorem pc69w99 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored98 stored100 rfl rfl

private theorem pc69w98 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w99 stored99 rfl rfl




private theorem pc69w108 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w107 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w108 stored97 rfl rfl
private theorem pc69w109 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 stored98 stored99 rfl rfl
private theorem pc69w106 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w107 pc69w109 rfl rfl
private theorem pc69w111 : PetersenPackedPin.project extra69 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored98 stored100 rfl rfl
private theorem pc69w110 : PetersenPackedPin.project extra69 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w111 pc69w108 rfl rfl
private theorem pc69w112 : PetersenPackedPin.project extra69 (0xffffffffcccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w107 pc69w111 rfl rfl
private theorem pc69w114 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored100 rfl rfl
private theorem pc69w113 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w114 stored99 rfl rfl
private theorem pc69w116 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored98 stored99 rfl rfl
private theorem pc69w115 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w107 pc69w116 rfl rfl
private theorem pc69w117 : PetersenPackedPin.project extra69 (0xffffffffcccccccc0000000000000000ffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w108 stored98 rfl rfl
private theorem pc26w118 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w120 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w119 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w120 stored0 rfl rfl
private theorem pc34w121 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w123 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w122 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc34w123 stored16 rfl rfl
theorem b3_1428 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1428 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,true),(3,true))] s3_1428 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons pc26w0 rfl)))))))))) (by decide +kernel)
theorem b3_1429 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1429 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1429 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w11 rfl))))))))) (by decide +kernel)
theorem b3_1430 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1430 := by
  apply PetersenIndexedNode.close (bank := [s4_426,a4399,a4400,s4_2499,s4_506,a4133,a4401,s4_2800,s4_850,a4402,a4403,a4404,a4405,s4_317,a4406,a4407,a4408,s4_244,a4409,a4410,s4_4,a4411,s4_957,a4412,a4146,a4413,a4148,s4_500,s4_404,s4_2937,s4_2939,s4_961,s4_2972,s4_964,a4414,s4_974,s4_925,a4415,s4_959,s4_915,s4_913]) (PetersenIndexedNode.reasons 256 17 426 0x18888480821012101085044202622210a0908888404240421012005100275000210114100a0008010a820141008404801321010e060a080381812021c1804808381838300e0604808504012021202050404800210112100900048082420120208404282021010a0209080280012020a0805000280814100a020480848401202200485040282028200e0c0706080129c180e0c0a080282014101181828204602210119180840446063230108188404141021010901028202400140409080480024041210090105010141014041511048402420282005040282054440a0805040a08024201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180898180602030112021898048082606313009018480803010180a004406020301282004c4426228011898884c44a080030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c142820030101809242403010180a101107028301490920e0520248404018080c048504030101809202085804808214110b0090144808018080c05450403010180a82004c4826245141098904c48a080018080c052504030101809410026221301494104c4406225040018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c050a0a0302018121011070483024282a0e09080a8404018100c0892120302018112020c2c0480824849858090124808018100c09430203020181282004240212050c0884804240a080018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c080602212001800181006040300018080c0806020604109001812003f001e800ea1012003884048010c008140408404800da1010e061001938181202200304808381840068e0604808800b92022002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_426 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_317 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2414 theta)
    · exact b4_2499 theta
    · exact b4_506 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_104 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2632 theta)
    · exact b4_2800 theta
    · exact b4_850 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_244 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2304 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2562 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_426 theta)
    · exact b4_317 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2414 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2499 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_850 theta)
    · exact b4_244 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2304 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2562 theta)
    · exact b4_4 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2670 theta)
    · exact b4_957 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_506 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_104 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2632 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2800 theta)
    · exact b4_500 theta
    · exact b4_404 theta
    · exact b4_2937 theta
    · exact b4_2939 theta
    · exact b4_961 theta
    · exact b4_2972 theta
    · exact b4_964 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_925 theta)
    · exact b4_974 theta
    · exact b4_925 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_974 theta)
    · exact b4_959 theta
    · exact b4_915 theta
    · exact b4_913 theta
theorem b3_1431 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1431 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(6,true))] s3_1431 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w25 (PetersenWireProjection.cons pc30w22 rfl)))))))))) (by decide +kernel)
theorem b3_1432 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1432 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1432 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xfafafafa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w34 (PetersenWireProjection.cons pc2w33 rfl)))))))))) (by decide +kernel)
theorem b3_1433 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1433 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1433 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w45 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w38 (PetersenWireProjection.cons pc41w35 rfl)))))))))) (by decide +kernel)
theorem b3_1434 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1434 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(3,true))] s3_1434 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w46 rfl))))))))) (by decide +kernel)
theorem b3_1435 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1435 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1435 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfafafafa] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w33 (PetersenWireProjection.cons pc2w47 rfl)))))))))) (by decide +kernel)
theorem b3_1436 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1436 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_1436 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w50 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w49 rfl)))))))))) (by decide +kernel)
theorem b3_1437 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1437 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,true),(1,true))] s3_1437 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1438 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1438 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(3,true),(4,true))] s3_1438 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w54 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1439 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1439 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(3,true),(6,true))] s3_1439 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w55 rfl)))))))))) (by decide +kernel)
theorem b3_1440 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1440 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_1440 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w66 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w56 rfl)))))))))) (by decide +kernel)
theorem b3_1441 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1441 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1441 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w68 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1442 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1442 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_1442 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w78 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w49 rfl)))))))))) (by decide +kernel)
theorem b3_1443 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1443 := by
  apply PetersenIndexedNode.close (bank := [a4416,s4_2500,s4_507,a4417,a4418,a4419,a4420,a4421,a4422,s4_958,a4423,a4424,a4425,s4_966,a4426,s4_975,s4_930,a4427,s4_956,a4381]) (PetersenIndexedNode.reasons 256 17 420 0x6222108088404a2026141288098888c2824222288088404420251014004d400084045040280014404a08051012101200248404210128200840448087060120208404e0c0210112021410048084808141012000a20248402400120209080480828808a080a202280824200a0004202282014000a020504028081080921004202800814100a080a08038301c18200227060383028200a080504055050a0815404a2026460288095414c8c05105288085040a20224040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028204202018090800a202424021001080884804202288080c0406022606018080c0442026260108089818c4c02406108080c0406028007212010900a08003010180a001e0602030128201090084802a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406025101098910602840441c0a0c05440483815001210104c48a00221010989084044808313012020840462602101120204c484808514120e040602a080131200c05450426241312282010702a0804941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260428280c080604a20241c1288090a0a83824202a880806040302248480c080604420230b010808921261602404908080604030250c0a0e094300a080018100c09430203020181282010704a08028a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c0907020302018109890424021208006c00314040a202150528808c4442a0a31011080a0014420231114002c8444420215051080a001300081080a82005414210138300a828541450401d0d0e828e0c03a1a150d1410054142a0a14104001c5404484015050a80850402a0a150512102000c484013110a8284c0406028002018084c4500050311018085414060213124000c4c48838115050a8284c482a0a140520e060004280a10900a82846040302800000c0842410001109000c0854140302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_318 theta)
    · exact b4_2500 theta
    · exact b4_507 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2630 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_245 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2560 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_427 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2420 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2707 theta)
    · exact b4_958 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_120 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2801 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2941 theta)
    · exact b4_966 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_931 theta)
    · exact b4_975 theta
    · exact b4_930 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_976 theta)
    · exact b4_956 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_907 theta)
theorem b3_1444 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1444 := by
  apply PetersenIndexedNode.close (bank := [s4_428,a4428,a4429,s4_2501,s4_508,a4430,a4431,s4_2802,s4_851,a4432,a4433,a4434,a4435,s4_319,a4436,a4437,a4438,s4_246,a4439,a4440,a4441,a4442,s4_969,a4443,a4444,a4445,a4446,a4447,s4_972,a4448,s4_977,s4_932,a4449,s4_968,a4450,a4451,s4_973]) (PetersenIndexedNode.reasons 256 17 420 0x622212021880884046444210118888c888422221010901084048011c0089400084045040280020048a0805040210120042840431112820084044808706010808c444e0c0311112021410048084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808800f94100a080a08038301c18200407060383028200a080504046060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c040602800e818080c04a08013110988a003c26221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301311100c0406024808313012020c444626024051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800e4006d40408404800a21010c44500193111120220030480831114006884444808800b92022002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_428 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_319 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2421 theta)
    · exact b4_2501 theta
    · exact b4_508 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_122 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2631 theta)
    · exact b4_2802 theta
    · exact b4_851 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_246 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2299 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2561 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_428 theta)
    · exact b4_319 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2421 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2501 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_851 theta)
    · exact b4_246 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2299 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2561 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_4 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2822 theta)
    · exact b4_969 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_508 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_122 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2631 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2802 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2970 theta)
    · exact b4_972 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_932 theta)
    · exact b4_977 theta
    · exact b4_932 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_977 theta)
    · exact b4_968 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_395 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_396 theta)
    · exact b4_973 theta
theorem b3_1445 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1445 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1445 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w48 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w78 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1446 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1446 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(3,true))] s3_1446 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w54 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1447 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1447 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(6,true))] s3_1447 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w25 rfl)))))))))) (by decide +kernel)
theorem b3_1448 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1448 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(3,true),(6,true))] s3_1448 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w55 rfl)))))))))) (by decide +kernel)
theorem b3_1449 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1449 := by
  apply PetersenIndexedNode.close (bank := [s4_429,a4452,a4453,s4_2502,s4_509,a4454,a4455,s4_2803,s4_852,a4456,a4457,a4458,a4459,s4_320,a4460,a4461,s4_892,a4462,a4463,s4_3046,s4_7,a4464,s4_980,a4465,a4466,a4467,a4468,s4_3072,s4_982,a4469,s4_983,s4_922,s4_984,s4_909,s4_908]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108092404c28249013111185048444490110808840500228010a80020038a08050402480a002c9202311128200c4444202706010808c444e0c0311110809410042024901141012000840448402400124049080490121010a0808404210124200a00048082820140008404504021011202121004808800f94100a080a08038301c18200407060383028200a08050404d050a081340492026460248093414c8c04905248085040920224040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a0805040504015110e08131102a221511141005040282042020180908009202424021001080884804202248080c0406022606018080c0442026260108089818c4c02406108080c040602800e818080c04a08013110988a003c26221311282000c0406022a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602490100c450602840441c0a0c052404838148012101006229002210100c44840448086160120208404c2c021011202006225002514100c440622a080131a098d145042634131a2820006220311494120e0406025040018880c052504031101889410107025040151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311428280c080604920241c1248090a0a83824202a480806040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614800e4006d40409202800a24808c445001931111080a00304202311140068c4444202800b9080a002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a00100602131a400184c680311800280c444c690007131a00c460008031110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_429 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_325 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2415 theta)
    · exact b4_2502 theta
    · exact b4_509 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_111 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2634 theta)
    · exact b4_2803 theta
    · exact b4_852 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_248 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2302 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2564 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_432 theta)
    · exact b4_320 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2417 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2505 theta)
    · exact b4_892 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_29 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2305 theta)
    · exact b4_3046 theta
    · exact b4_7 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2674 theta)
    · exact b4_980 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_514 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_108 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2768 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2806 theta)
    · exact b4_3072 theta
    · exact b4_982 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_927 theta)
    · exact b4_983 theta
    · exact b4_922 theta
    · exact b4_984 theta
    · exact b4_909 theta
    · exact b4_908 theta
theorem b3_1450 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1450 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1450 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w80 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1451 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1451 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1451 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1452 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1452 := by
  apply PetersenIndexedNode.close (bank := [s4_430,a4470,a4471,s4_2503,s4_511,a4472,a4473,s4_2804,s4_853,a4474,a4475,a4476,a4477,s4_321,a4478,a4479,a4480,s4_226,a4481,s4_3129,s4_9,a4482,s4_985,a4483,a4484,a4485,a4486,s4_3134,s4_987,a4487,a4488,a4489,s4_988,s4_921,s4_989,s4_911,s4_910]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404310110808c88842023111191108444420212021080900248011a80020038a080504021012002c8404381828200e0604808706012020e060e0c0381812021410048084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808801094100a080a08038301c18200447060383028200a080504046060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c040602800f818080c04a08013110988a004026221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301210900c0406024808800e920208425001e24051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800e4006d40408404800a21010e061001938181202200304808381840068e0604808800b92022002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_430 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_326 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2416 theta)
    · exact b4_2503 theta
    · exact b4_511 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_114 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2635 theta)
    · exact b4_2804 theta
    · exact b4_853 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_249 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2303 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2565 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_433 theta)
    · exact b4_321 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2418 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2506 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_890 theta)
    · exact b4_226 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2660 theta)
    · exact b4_3129 theta
    · exact b4_9 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2677 theta)
    · exact b4_985 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_515 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_110 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2769 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2807 theta)
    · exact b4_3134 theta
    · exact b4_987 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_903 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1001 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_928 theta)
    · exact b4_988 theta
    · exact b4_921 theta
    · exact b4_989 theta
    · exact b4_911 theta
    · exact b4_910 theta
theorem b3_1453 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1453 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1453 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w84 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1454 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1454 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1454 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w84 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))) (by decide +kernel)
theorem b3_1455 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1455 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1455 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons pc1w87 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1456 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1456 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1456 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w90 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1457 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1457 := by
  apply PetersenIndexedNode.close (bank := [s4_431,a4490,a4491,s4_2504,s4_513,a4492,a4493,s4_2805,s4_854,a4494,a4495,a4496,a4497,s4_286,a4498,a4499,a4500,s4_247,a4501,a4502,a4503,a4504,s4_996,a4505,a4506,a4507,a4508,a4509,s4_998,a4510,s4_1002,a4511,s4_999,s4_926,s4_1000,a4512,a4513]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404310110808c88842023111191108444420212021080900248011a80020038a080504021012002c8404381828200e0604808706012020e060e0c0381812021410048084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808801094100a080a08038301c18200447060383028200a080504046060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c040602800f818080c04a08013110988a004026221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301210500c0406024808800e908208415001e21051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800e4006d40408404800a21010e061001938181202200304808381840068e0604808800b92022002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_431 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_327 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2419 theta)
    · exact b4_2504 theta
    · exact b4_513 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_125 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2633 theta)
    · exact b4_2805 theta
    · exact b4_854 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_250 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2300 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2563 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_843 theta)
    · exact b4_286 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2662 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3130 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_855 theta)
    · exact b4_247 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2301 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2566 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_9 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2677 theta)
    · exact b4_996 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_522 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_118 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2636 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2837 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3134 theta)
    · exact b4_998 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_904 theta)
    · exact b4_1002 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_929 theta)
    · exact b4_999 theta
    · exact b4_926 theta
    · exact b4_1000 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_910 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_911 theta)
theorem b3_1458 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1458 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1458 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons pc1w92 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1459 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1459 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1459 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xffff0000,0xff00ff00,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w94 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1460 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1460 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1460 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w106 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w98 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1461 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1461 := by
  apply PetersenIndexedNode.close (bank := [s4_435,a4514,a4515,s4_2507,s4_525,a4516,a4517,s4_2799,s4_857,a4518,a4519,a4520,a4521,s4_328,a4522,a4523,a4524,s4_251,a4525,a4526,s4_960,s4_19,a4527,a4078,a4528,s4_155,a4529,a4079,s4_3,a4530,s4_1008,a4531,s4_1006,s4_1003,s4_1009,a4532,s4_1007]) (PetersenIndexedNode.reasons 256 17 426 0x18888480862022101185048404622230a090888840424042101200462a0a5000210114100a00080122820141008404150521010c4442a0a310112021c1806202311138300c4444808150512021202050404800210112100900048082420120208404282021010a0209080280012020a0805000280814100a0204808484012020743450401d050a828e0c02a0a1d0d1c18054342a0a28200a8291818282046022101191808404460632301081884041410210109010282024001404090804800240412100901050101410140405414484015012820050402a0215050a0805414a08024201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180898180602030112021898048082606313009018480803010180a0042060203010a8284c4426028011098880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a003e26244180a101107028301801020e0507028404131221010c444262421001202084804200311110900c4444808131212020541442401505282004c4826241505098905014a08021200a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0442400301212004c4826200301098900c0484802120109010a0a0302018121011070484044282a0e09080a8404018100c0892120302018112020c2c0480824849858090124808018100c094302030201810a8284240230250c08848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090098900604030221a080c0806042624109008482003d001d49092101200388404311140068c4444808800c92020c445001b210112022003042021505400584202a080800a88404541500171505282020028a080383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848400301400280c0484808004a12000c05000b0301212020010848013124001806024240800280c044c49000713121090200084240018140008060483828000a0e0806050003018120e0a00008382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_435 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_331 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2412 theta)
    · exact b4_2507 theta
    · exact b4_525 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2626 theta)
    · exact b4_2799 theta
    · exact b4_857 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_252 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2297 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2567 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_436 theta)
    · exact b4_328 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2409 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2508 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_858 theta)
    · exact b4_251 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2294 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2568 theta)
    · exact b4_960 theta
    · exact b4_19 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2668 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2792 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_505 theta)
    · exact b4_155 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2629 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2819 theta)
    · exact b4_3 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2912 theta)
    · exact b4_1008 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_645 theta)
    · exact b4_1006 theta
    · exact b4_1003 theta
    · exact b4_1009 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_912 theta)
    · exact b4_1007 theta
theorem b3_1462 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1462 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1462 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w112 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w110 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1463 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1463 := by
  apply PetersenIndexedNode.close (bank := [s4_437,a4533,a4534,s4_2509,s4_704,a4535,a4339,s4_2798,s4_859,a4536,a4537,a4538,a4539,s4_332,a4540,a4541,a4542,s4_253,a4543,a4544,s4_902,s4_204,a4545,a4350,a4546,s4_97,a4547,a4367,s4_3,a4548,s4_1016,s4_1013,s4_1017,a4549,s4_1015]) (PetersenIndexedNode.reasons 256 17 426 0x18888420221012101185048404622230a0908888404210110809404021015000210114100a00050102820140408404108088404c4442101108090809c180420231113830084444202108088405202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a020420248401080862225040188088404e0c0210118889c18042222101282008405181828204602210119180840446063230108188404141021010901028202400108089080480024041210090104202141010808501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a0810808060242002404109008400420221201080890100301018089818060203011080989804202260631300901842020301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a004262604180a101107028301801120e050702840431302101084048381210112020c4c048082101189808404480841c09202054148381150508404c4c021011505189805414210141c08840525046260313014102003e5040494140081210450403130141005444626015110a08117122820151122e245444282031300a0800c046260030121200ccc866600301199900c0484803130189810a0a0302018121011070484044282a0e09080a8404018100c0892120302018110808c2c0420224849858090124202018100c084202030210800a0204240210010808848042022808018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c09070221201090189800604030241c080c0806046260109008482003d001d4909210120038840421014006884044808800c920208405001b2101120220030480815054005854142101800a884045415001715050840600282101383040048e0c05040800894100e0c10013383014102002050401511400385444282080068a0805445000f15110a082001828200301400280c0484808004a12000c05000b0301212020010848031304001806028381800280c04c4c10007313020e0600088381018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_437 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_355 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2397 theta)
    · exact b4_2509 theta
    · exact b4_704 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_64 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2798 theta
    · exact b4_859 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_271 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2292 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2555 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_451 theta)
    · exact b4_332 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2387 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2528 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_864 theta)
    · exact b4_253 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2271 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2556 theta)
    · exact b4_902 theta
    · exact b4_204 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2692 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2824 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_546 theta)
    · exact b4_97 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2624 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2812 theta)
    · exact b4_3 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2916 theta)
    · exact b4_1016 theta
    · exact b4_1013 theta
    · exact b4_1017 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_654 theta)
    · exact b4_1015 theta
theorem b3_1464 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1464 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1464 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w115 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w113 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1465 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1465 := by
  apply PetersenIndexedNode.close (bank := [s4_438,a4550,a4551,s4_2510,s4_546,a4516,a4552,s4_2799,s4_860,a4553,a4554,a4555,a4556,s4_333,a4557,a4558,a4559,s4_254,a4560,a4561,s4_960,s4_192,a4527,s4_1021,a4562,a4563,s4_1025,a4546,a4076,a4547,a4564,s4_3,a4565,s4_1024,a4566,s4_1030,s4_1019,a4567,a4568,a4569,s4_1023]) (PetersenIndexedNode.reasons 256 17 426 0x1888848086101210118504c202622230a0908888404240421012004f00265000210114100a00080142820141008404800ba1010c444a080311112021c180480831113830084444808504012021202050404800210112100900048082420120208404282021010a0209080280012020a0805000280814100a020480848401202200485040282028200e0c0706080129c180e0c0a080282014101181828204602210119180840446063230108188404141021010901028202400140409080480024041210090105010141014041511048402420282005040282054440a0805040a08024201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180898180602030112021898048082606313009018480803010180a004406020301282004c4426228011898884c44a080030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c142820030101809242403010180a101107028301490920e0520248404018080c04c4440301018092020c4c0480831111898090144808018080c05450403010180a82004c4826245141098904c48a080018080c052504030101809410026221301494104c4406225040018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c050a0a0302018121011070483024282a0e09080a8404018100c0892120302018112020c2c0480824849858090124808018100c09430203020181282004240212050c0884804240a080018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c080602212001800181006040300018080c080602060410900181200430020501021012003e840431114007484044808800e10808c445001e31111202200364808800bc00584202a080800a8840600350019800c282020028a080383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_438 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_333 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2398 theta)
    · exact b4_2510 theta
    · exact b4_546 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2624 theta)
    · exact b4_2799 theta
    · exact b4_860 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_254 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2290 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2569 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_438 theta)
    · exact b4_333 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2398 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2510 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_860 theta)
    · exact b4_254 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2290 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2569 theta)
    · exact b4_960 theta
    · exact b4_192 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2668 theta)
    · exact b4_1021 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2937 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2823 theta)
    · exact b4_1025 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_546 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_97 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2624 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2799 theta)
    · exact b4_3 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2917 theta)
    · exact b4_1024 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1019 theta)
    · exact b4_1030 theta
    · exact b4_1019 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1030 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_913 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_914 theta)
    · exact b4_1023 theta
theorem b3_1466 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1466 := by
  apply PetersenIndexedNode.close (bank := [s4_439,a4570,a4571,s4_2511,s4_547,a4430,a4572,s4_2802,s4_861,a4573,a4574,a4575,a4576,s4_334,a4577,a4578,a4579,s4_255,a4580,a4581,a4441,a4582,s4_1026,a4583,a4444,a4584,a4446,a4585,s4_1029,a4586,s4_1031,s4_1020,a4587,a4588,a4589]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404310110808c88842023111191108444420212021080900228010a80020038a080504021012002c8404211128200844448087060120208444e0c0211112021410048084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808800f94100a080a08038301c18200407060383028200a080504046060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c040602800e818080c04a08013110988a003c26221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301211100c04060248082130120208444426024051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800e4006d40408404800a21010844500192111120220030480821114006884444808800b92022002d00151080a820200282101383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c060008030110904000842400302800080c0842410003109000c0a00000302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_439 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_334 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2399 theta)
    · exact b4_2511 theta
    · exact b4_547 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_122 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2625 theta)
    · exact b4_2802 theta
    · exact b4_861 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_255 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2291 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2570 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_439 theta)
    · exact b4_334 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2399 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2511 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_861 theta)
    · exact b4_255 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2291 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2570 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_4 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2716 theta)
    · exact b4_1026 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_547 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_122 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2625 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2802 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2972 theta)
    · exact b4_1029 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1020 theta)
    · exact b4_1031 theta
    · exact b4_1020 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1031 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_397 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_398 theta)
theorem b3_1467 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1467 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1467 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w107 (PetersenWireProjection.cons pc69w117 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1468 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1468 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1468 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w119 (PetersenWireProjection.cons pc26w118 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1469 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1469 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1469 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w122 (PetersenWireProjection.cons pc34w121 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
