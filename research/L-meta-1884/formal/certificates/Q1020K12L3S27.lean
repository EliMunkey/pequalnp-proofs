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
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S20
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S69
import Q1020K12L4S71
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc30w3 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl

private theorem pc30w2 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w3 stored10 rfl rfl



private theorem pc30w10 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl




private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl

private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc34w14 stored18 rfl rfl



private theorem pc34w21 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl




private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl

private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl



private theorem pc26w32 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc30w33 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w34 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl




private theorem pc3w37 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w41 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w40 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w41 stored36 rfl rfl











private theorem pc1w54 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored57 stored64 rfl rfl
private theorem pc1w56 : PetersenPackedPin.project cycle1 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0x44444444 := PetersenWireProjection.derive 1 stored63 stored64 rfl rfl
private theorem pc1w53 : PetersenPackedPin.project cycle1 (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 pc1w54 pc1w56 rfl rfl
private theorem pc1w57 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc3w59 : PetersenPackedPin.project cycle3 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored40 rfl rfl
private theorem pc3w60 : PetersenPackedPin.project cycle3 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored39 stored40 rfl rfl
private theorem pc3w58 : PetersenPackedPin.project cycle3 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w59 pc3w60 rfl rfl
private theorem pc1w62 : PetersenPackedPin.project cycle1 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored59 stored64 rfl rfl
private theorem pc1w61 : PetersenPackedPin.project cycle1 (0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc1w54 pc1w62 rfl rfl
private theorem pc1w64 : PetersenPackedPin.project cycle1 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored58 stored64 rfl rfl
private theorem pc1w63 : PetersenPackedPin.project cycle1 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc1w54 pc1w64 rfl rfl







private theorem pc69w72 : PetersenPackedPin.project extra69 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 stored98 stored100 rfl rfl
private theorem pc69w74 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w71 : PetersenPackedPin.project extra69 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc69w72 pc69w74 rfl rfl

private theorem pc69w77 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w74 stored97 rfl rfl
private theorem pc69w76 : PetersenPackedPin.project extra69 (0xccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w77 pc69w72 rfl rfl







private theorem pc73w85 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w87 : PetersenPackedPin.project extra73 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored131 stored135 rfl rfl
private theorem pc73w84 : PetersenPackedPin.project extra73 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w85 pc73w87 rfl rfl

private theorem pc73w90 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffff33333333000000003333333300000000 : BitVec 256) = 0xeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 pc73w87 stored129 rfl rfl
private theorem pc73w89 : PetersenPackedPin.project extra73 (0xccccccccffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w90 pc73w85 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w60 stored33 rfl rfl
private theorem pc3w91 : PetersenPackedPin.project cycle3 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w92 pc3w59 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w95 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w94 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w95 stored8 rfl rfl
private theorem pc30w96 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w97 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w98 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w99 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w100 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w102 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc30w103 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored9 stored10 rfl rfl
private theorem pc30w101 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w102 pc30w103 rfl rfl
private theorem pc30w104 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 3 pc30w103 stored8 rfl rfl
private theorem pc30w106 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xf0f0f0f030303030f0f0f0f030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w102 pc30w106 rfl rfl
private theorem pc30w107 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffff55005500ffffffff55005500 := PetersenWireProjection.derive 3 pc30w106 stored8 rfl rfl
private theorem pc30w108 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaa00000000ffaaffaa := PetersenWireProjection.derive 1 pc30w34 stored8 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w102 pc30w34 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff000000000fff0fff0 := PetersenWireProjection.derive 1 pc30w98 stored8 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w102 pc30w98 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafa00000000fafafafa := PetersenWireProjection.derive 1 pc30w113 stored8 rfl rfl
private theorem pc30w114 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w102 pc30w113 rfl rfl
private theorem pc30w115 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc30w116 : PetersenPackedPin.project extra30 (0xffffffffcccccccc0000000000000000ffffffffcccccccc : BitVec 256) = 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a := PetersenWireProjection.derive 1 pc30w34 stored9 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0xffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xf0f0f0f0f000f000f0f0f0f0f000f00 := PetersenWireProjection.derive 1 pc30w99 stored9 rfl rfl
private theorem pc30w119 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w118 : PetersenPackedPin.project extra30 (0xffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a := PetersenWireProjection.derive 1 pc30w119 stored9 rfl rfl
theorem b3_1134 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1134 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1134 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w2 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1135 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1135 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1135 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w21 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w13 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1136 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1136 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1136 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1137 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1137 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1137 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons pc30w33 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1138 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1138 := by
  apply PetersenIndexedNode.close (bank := [a4306,s4_2496,s4_305,a4307,s4_755,s4_802,a4308,s4_790,s4_548,a4309,a4310,s4_794,s4_696,s4_684,s4_686,s4_797,s4_687,s4_795,s4_633,s4_796,s4_603,s4_798,s4_753,s4_615,s4_585,s4_800,s4_786,s4_560,s4_789,a4311,a4161,s4_556,s4_549,s4_799]) (PetersenIndexedNode.reasons 256 17 414 0x140402a0a1505210114104840450102820940408404150521011888842226110210120040840462224008588888404211121012003f001e21010a828844442025010185050602840441c0a0c0540408381501021010c2828404150520e044203001d30a0884045414614115054007107028381211120e048445001b30a09850484446141211140069070250304808141012000840448402400120209080480821010a08084041d0d2420074142a0a28200a82874345040150d0a82921002a0a381824200e040422228201c080e060504038181088921004222800c14100a080614138301c10200327060283018504a080504046060a081180884046460210111818c8c04206210105040840415054005c5404a08214100a8085414282015052820a002ca082800a0a0805040422224201a082002a48402420108885040282045c4921009080614114100a08117122820141018504908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406028009018080c042a0a13110980a0026262203110a8280c0406023a1a018080c044222626010888e868c4c0381a108880c04060232a2a1200ca826141030101808ca8a0602030118505090061412a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602428280c080604840441c1210110a0a83824202a101006040302800800c0806042a0a109008c0a0022212010900a82806040302800700c080604422230b018482001e616010b0108880604030230a0c0034c280c2c0018100c08c2820302018130b020018c2c028a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b022524109201808060403028005c002924248404131221010541500091505282084c4826241505098905014a08280040a0288444262421101c0c084c0422021111098084447030131209892000f00060180985044c4803018002098904c4850401b1a0d892000a3634131a141004c4826241511098905440282080010a0805445000314110a0804c4828200301109800c0484801312098800c04262403012120084c0426001810989006042120800008480060500010181084804c482120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_348 theta)
    · exact b4_2496 theta
    · exact b4_305 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2521 theta)
    · exact b4_755 theta
    · exact b4_802 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2811 theta)
    · exact b4_790 theta
    · exact b4_548 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2754 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3011 theta)
    · exact b4_794 theta
    · exact b4_696 theta
    · exact b4_684 theta
    · exact b4_686 theta
    · exact b4_797 theta
    · exact b4_687 theta
    · exact b4_795 theta
    · exact b4_633 theta
    · exact b4_796 theta
    · exact b4_603 theta
    · exact b4_798 theta
    · exact b4_753 theta
    · exact b4_615 theta
    · exact b4_585 theta
    · exact b4_800 theta
    · exact b4_786 theta
    · exact b4_560 theta
    · exact b4_789 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_67 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_557 theta)
    · exact b4_556 theta
    · exact b4_549 theta
    · exact b4_799 theta
theorem b3_1139 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1139 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1139 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w41 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w40 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w37 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1140 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1140 := by
  apply PetersenIndexedNode.close (bank := [s4_419,a4312,a4313,a4314,a4315,a4316,s4_817,s4_486,a4317,a4318,a4319,a4320,s4_307,a4321,a4322,s4_494,s4_236,a4323,a4324,s4_818,a4325,a4326,s4_821,s4_521,a4327,a4328,a4329,a4330,s4_124,a4331,a4332,a4333,s4_820,s4_694,s4_644,s4_621,s4_822,s4_579,s4_823,a4334,s4_824,a4335,a4336]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404b10150808c889420231111911285444202120250808a0201080a80010808a0805000280814100a0204202084044202622210808840490126140308098888c28062222404884044202901028202400108089080480024041210090104202141010808501148401400490125040280094044a08050112404a42009012311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a08108084809141012004a02248402400920249080480928088a080a022280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0d0301018089012c4c02404930358980480d2404818080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c05002a8014a0c060040838141c0a1012000c8404311120e04c4444809616012024c444c2c031111202507024809150520e04541421018013884045415002815050840507022101494120e05250050408012941012505002648411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808011a12000c05002403012120107028480428280c080604840441c1210110a0a83824202a101006040302240480c080604622230b0108089012616024049888806040302108080c08420028081090084004202212010808a02006040302282000c0806047060098904c08a080131201891c18006040302242000c0806042820058502c0890800b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042410022018100c09070203020181400844240212080104007d24248404800221010c445001d31111202600384809311140078c4444809800d92024541500191505084060030210115054006854142101800b884060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_419 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_329 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2598 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3049 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_7 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2615 theta)
    · exact b4_817 theta
    · exact b4_486 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_267 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2316 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2542 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_445 theta)
    · exact b4_307 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2394 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2524 theta)
    · exact b4_494 theta
    · exact b4_236 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2285 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2282 theta)
    · exact b4_818 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_3178 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2549 theta)
    · exact b4_821 theta
    · exact b4_521 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_212 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2702 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2831 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_541 theta)
    · exact b4_124 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2643 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2817 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3062 theta)
    · exact b4_820 theta
    · exact b4_694 theta
    · exact b4_644 theta
    · exact b4_621 theta
    · exact b4_822 theta
    · exact b4_579 theta
    · exact b4_823 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_567 theta)
    · exact b4_824 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_647 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_651 theta)
theorem b3_1141 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1141 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1141 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons pc1w53 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1142 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1142 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1142 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w41 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w58 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1143 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1143 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1143 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xaaaaaaaa,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w61 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1144 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1144 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1144 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xaaaaaaaa,0x0] (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w63 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1145 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1145 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1145 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w76 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w71 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1146 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1146 := by
  apply PetersenIndexedNode.close (bank := [s4_416,a4337,a4338,s4_2497,s4_704,a4065,a4339,s4_2792,s4_488,a4340,a4341,a4342,a4343,s4_308,a4344,a4345,s4_498,s4_237,a4346,a4347,s4_829,s4_3101,a4348,s4_833,s4_528,s4_204,a4349,a4350,s4_533,s4_155,a4351,a4079,s4_3,a4352,s4_832,a4353,s4_831]) (PetersenIndexedNode.reasons 256 17 426 0x18888420221012101185048404622230a0908888404210110809c0c02a0a5000210114100a000703028201c0c08404150521010c4442a0a308090808c282610131111850484444202150510809202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a0204202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a8291818282046022101191808404460632301081884041410210109010282024001080890804800240412100901042021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a081080806024200240410900840042022120108089010030101808981806020301108098980420226063130090184202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a004626244180a101107028301801220e05070284041312210108404262421011202185804808210130b0084044808131212020541483811505185044c4826241505098905014614141c08a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0483810301212004c4826200301098900c04848041c0a12010a0a0302018121011070484044282a0e09080a8404018100c0892120302018110808c2c0420224849858090124202018100c08c282030201810a8284240230230a08848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c09070221201090098900604030241c080c0806042624109008482004500214909210120040840421014007884044808800e920208405001f2101120220038480815054006842026141800c884045415001b15051850600306141800a4004e00245040800894102002f0016800a9410200205040141040038504048408006921005041000f141012102001848400301400280c0484808004a12000c05000b0301212020010848013124001806028381800280c044c490007131220e0600088381018140008060461608000985800605000301811858200006160)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_416 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_354 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2404 theta)
    · exact b4_2497 theta
    · exact b4_704 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2792 theta
    · exact b4_488 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_270 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2312 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2545 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_449 theta)
    · exact b4_308 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2389 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2527 theta)
    · exact b4_498 theta
    · exact b4_237 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2277 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2276 theta)
    · exact b4_829 theta
    · exact b4_3101 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2554 theta)
    · exact b4_833 theta
    · exact b4_528 theta
    · exact b4_204 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2693 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2824 theta)
    · exact b4_533 theta
    · exact b4_155 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2640 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2819 theta)
    · exact b4_3 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2898 theta)
    · exact b4_832 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_653 theta)
    · exact b4_831 theta
theorem b3_1147 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1147 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_1147 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w89 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons pc73w84 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_1148 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1148 := by
  apply PetersenIndexedNode.close (bank := [s4_418,a4354,a4355,s4_2498,s4_704,a4093,a4339,s4_2794,s4_490,a4356,a4357,a4358,a4359,s4_309,a4360,a4361,s4_499,s4_238,a4362,a4363,s4_505,s4_222,a4364,a4105,a4365,s4_97,a4366,a4367,s4_3,a4368,s4_838,s4_835,s4_839,a4369,s4_840,a4370,s4_837]) (PetersenIndexedNode.reasons 256 17 426 0x1c0c0420221012101185048404703030a0940c08404210110809404021015000210114100a00050102820140408404108088404c4442101108090809c180610131113830084444202108088405202050404800210112100900048082420120208404282021010a4249080290110808a08042022909141008424420248401080862225040188088404e0c0210118889c18042222101282008405181828204602210119180840446063230108188404141021010941428202501108089080420225051210084144202141010808501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a081080806024200240410900840042022120108089010030101808e8680602030110809898042023a1a31300e06842020301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a004642404180a101107028301801220e05070284042120210108404838121011c0c0848070302101109008404703041c09202854144240150508406004221011505400885414210121200840525044240212014102003e5040494140081210450402120109005444424015110a08117122820151122e245444282021200a0800c0442400301212008c8846400301119100c0484802120109010a0a0302018121011070484044282a0e09080a8404018100c0993120302018110808c2c0420264c49858042c04202018100c084202030210800a0204240210010808848042022808018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090109000604030221a080c0806044240109008482003d001d4909210120038840421014006884047030800c920208405001b21011c0c20030703015054005854142101800a884045415001715050840600282101282040048a080706080089c180a081001328201c182002070601511400385444282080068a0805445000f15110a082001828200301400280c0484808004a12000c05000b0301212020010848021204001806028381800280c0484810007212020e0600088381018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_418 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_353 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2401 theta)
    · exact b4_2498 theta
    · exact b4_704 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2794 theta
    · exact b4_490 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_269 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2310 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2543 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_448 theta)
    · exact b4_309 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2388 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2526 theta)
    · exact b4_499 theta
    · exact b4_238 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2278 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2552 theta)
    · exact b4_505 theta
    · exact b4_222 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2694 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2832 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_543 theta)
    · exact b4_97 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2639 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2812 theta)
    · exact b4_3 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2898 theta)
    · exact b4_838 theta
    · exact b4_835 theta
    · exact b4_839 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_569 theta)
    · exact b4_840 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_652 theta)
    · exact b4_837 theta
theorem b3_1149 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1149 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1149 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w91 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w58 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1150 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1150 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true))] s3_1150 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf000f000f000f000f000f000f000f00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons pc30w93 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1151 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1151 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,true))] s3_1151 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf000f000f000f000f000f000f000f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons pc30w96 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1152 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1152 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false))] s3_1152 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w97 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1153 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1153 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true))] s3_1153 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w98 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1154 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1154 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true))] s3_1154 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w99 rfl)))))))))) (by decide +kernel)
theorem b3_1155 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1155 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true))] s3_1155 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w100 rfl)))))))))) (by decide +kernel)
theorem b3_1156 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1156 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_1156 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w101 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1157 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1157 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s3_1157 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff50505050ffffffff50505050] (PetersenWireProjection.cons pc30w101 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w104 rfl)))))))))) (by decide +kernel)
theorem b3_1158 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1158 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_1158 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1159 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1159 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(0,true),(6,true))] s3_1159 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff55005500ffffffff55005500] (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w107 rfl)))))))))) (by decide +kernel)
theorem b3_1160 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1160 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1160 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w109 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1161 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1161 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true))] s3_1161 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w109 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1162 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1162 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_1162 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w109 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1163 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1163 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1163 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons pc30w110 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1164 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1164 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true))] s3_1164 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w98 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1165 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1165 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_1165 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1166 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1166 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(2,true)),(false,(0,true),(6,true))] s3_1166 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafa00000000fafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons pc30w112 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1167 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1167 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(2,true))] s3_1167 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w113 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1168 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1168 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_1168 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1169 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1169 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(3,true),(6,true))] s3_1169 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w115 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w100 rfl)))))))))) (by decide +kernel)
theorem b3_1170 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1170 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1170 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1171 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1171 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1171 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w110 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1172 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1172 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(2,true)),(false,(0,true),(6,true))] s3_1172 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafa00000000fafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w112 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1173 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1173 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(0,true),(3,true))] s3_1173 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w116 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1174 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1174 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,true),(3,true))] s3_1174 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f000f000f0f0f0f0f000f00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w117 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1175 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1175 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(3,true),(0,true))] s3_1175 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w118 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
