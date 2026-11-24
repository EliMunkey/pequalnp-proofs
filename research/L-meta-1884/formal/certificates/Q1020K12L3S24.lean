import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
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
import Q1020K12L4S19
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S62
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S67
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc3w1 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w0 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w1 stored33 rfl rfl





private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w12 stored33 rfl rfl


private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl






private theorem pc26w22 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc3w23 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored33 stored35 rfl rfl
private theorem pc3w24 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w25 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w26 stored33 rfl rfl
private theorem pc3w27 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w29 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w29 stored33 rfl rfl


private theorem pc32w30 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl

private theorem pc32w33 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl





private theorem pc32w40 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w41 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl


private theorem pc34w42 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl

private theorem pc34w45 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl





private theorem pc34w52 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc3w53 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w10 stored34 rfl rfl
private theorem pc26w54 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl


private theorem pc30w56 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl

private theorem pc30w59 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl





private theorem pc30w66 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc32w67 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w68 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w69 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl


private theorem pc1w72 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl

private theorem pc1w71 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w72 stored58 rfl rfl





private theorem pc1w80 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl


private theorem pc74w81 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl

private theorem pc74w84 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl





private theorem pc74w91 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored113 stored119 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl
private theorem pc3w93 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w10 stored35 rfl rfl
private theorem pc3w94 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w12 stored35 rfl rfl
private theorem pc30w95 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w96 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc32w97 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc34w98 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w99 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc34w100 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc3w101 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored34 stored35 rfl rfl
private theorem pc3w102 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w10 stored36 rfl rfl
private theorem pc26w103 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w22 stored3 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w1 stored36 rfl rfl
private theorem pc3w105 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w12 stored36 rfl rfl
private theorem pc1w107 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl
private theorem pc1w108 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w106 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w107 pc1w108 rfl rfl
private theorem pc1w110 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored57 stored61 rfl rfl
private theorem pc1w111 : PetersenPackedPin.project cycle1 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored58 stored61 rfl rfl
private theorem pc1w109 : PetersenPackedPin.project cycle1 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 pc1w110 pc1w111 rfl rfl
private theorem pc3w113 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w112 : PetersenPackedPin.project cycle3 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w113 stored37 rfl rfl
private theorem pc3w114 : PetersenPackedPin.project cycle3 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w12 stored37 rfl rfl
private theorem pc1w116 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w115 : PetersenPackedPin.project cycle1 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc1w116 stored61 rfl rfl
private theorem pc1w118 : PetersenPackedPin.project cycle1 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored59 stored61 rfl rfl
private theorem pc1w117 : PetersenPackedPin.project cycle1 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 0 pc1w110 pc1w118 rfl rfl
private theorem pc3w120 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w120 stored38 rfl rfl
private theorem pc3w121 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w12 stored38 rfl rfl
theorem b3_1008 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1008 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1008 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w0 rfl))))))))) (by decide +kernel)
theorem b3_1009 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1009 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1009 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w11 rfl))))))))) (by decide +kernel)
theorem b3_1010 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1010 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(3,true))] s3_1010 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w13 rfl))))))))) (by decide +kernel)
theorem b3_1011 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1011 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_1011 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons pc3w23 rfl)))))))))) (by decide +kernel)
theorem b3_1012 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1012 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s3_1012 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons pc3w25 rfl)))))))))) (by decide +kernel)
theorem b3_1013 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1013 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_1013 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons pc3w27 rfl)))))))))) (by decide +kernel)
theorem b3_1014 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1014 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true))] s3_1014 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons pc3w28 rfl)))))))))) (by decide +kernel)
theorem b3_1015 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1015 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(3,true))] s3_1015 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w33 (PetersenWireProjection.cons pc32w30 rfl)))))))))) (by decide +kernel)
theorem b3_1016 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1016 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(5,true),(3,true))] s3_1016 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w33 (PetersenWireProjection.cons pc32w41 rfl)))))))))) (by decide +kernel)
theorem b3_1017 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1017 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(5,true),(7,true))] s3_1017 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w52 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w45 (PetersenWireProjection.cons pc34w42 rfl)))))))))) (by decide +kernel)
theorem b3_1018 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1018 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_1018 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w53 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w27 rfl)))))))))) (by decide +kernel)
theorem b3_1019 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1019 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(1,true))] s3_1019 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1020 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1020 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(3,true),(6,true))] s3_1020 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w66 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w56 rfl)))))))))) (by decide +kernel)
theorem b3_1021 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1021 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true))] s3_1021 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w68 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1022 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1022 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(5,true),(7,true))] s3_1022 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w52 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w69 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w42 rfl)))))))))) (by decide +kernel)
theorem b3_1023 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1023 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1023 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w80 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w71 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1024 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1024 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_1024 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc74w91 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w84 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w81 rfl)))))))))) (by decide +kernel)
theorem b3_1025 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1025 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_1025 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w93 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1026 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1026 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_1026 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w93 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w23 rfl)))))))))) (by decide +kernel)
theorem b3_1027 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1027 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1027 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w94 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1028 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1028 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_1028 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1029 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1029 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(6,true))] s3_1029 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons pc30w66 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w96 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w95 rfl)))))))))) (by decide +kernel)
theorem b3_1030 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1030 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true))] s3_1030 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w97 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1031 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1031 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(5,true))] s3_1031 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w52 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w99 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w98 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1032 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1032 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(7,true))] s3_1032 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w52 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w99 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w100 rfl)))))))))) (by decide +kernel)
theorem b3_1033 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1033 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s3_1033 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccc0000,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w102 (PetersenWireProjection.cons pc3w101 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1034 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1034 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_1034 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w102 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1035 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1035 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_1035 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w103 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1036 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1036 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_1036 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w102 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w23 rfl)))))))))) (by decide +kernel)
theorem b3_1037 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1037 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_1037 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w102 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w27 rfl)))))))))) (by decide +kernel)
theorem b3_1038 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1038 := by
  apply PetersenIndexedNode.close (bank := [s4_412,a4217,a4218,s4_2490,a4219,a4220,s4_699,s4_484,a4221,a4222,a4223,a4224,s4_297,a4225,a4226,s4_496,s4_230,a4227,a4228,s4_706,s4_3105,a4229,s4_709,s4_510,s4_209,a4230,a4231,s4_538,s4_108,a4232,a4233,a4234,s4_708,s4_620,s4_749,s4_574,s4_803,s4_566,s4_804,s4_651,s4_647]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108090808c282420231111850484444202108088404a0201088a80410808e0c0420228081c1809020420208445080870201088984048404614130809c080c28250202101084448404901028202400108089080480024041210090104202141010808501048401400084045040280014040a080501021012420084042111282008404c2827060108088444e0c0211130a094100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a0808404281824200a0404222282014080a0605040281810889210042229888242012100a0802820141026220504028202820121009080840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c042515030101808422226221088894544c4421151088818080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0500288013a0c060040838141c0a1012000c8404210120e04840448086160120208404c2c021011202107024808150d20e045434211180128844454350026150d0844507022111494120e05250050408011941012505002448411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808010a12000c05002203012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b0108089212616024049080806040302108880c08060428181090084404222212010888a0600604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b004240212080104007d242484048002210108405001d2101120220038480821014007884044808800d9202054350019150d0844600302111150d4006854342111800b884460027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_412 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_352 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2406 theta)
    · exact b4_2490 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_7 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2615 theta)
    · exact b4_699 theta
    · exact b4_484 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_268 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2317 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2541 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_446 theta)
    · exact b4_297 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2393 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2525 theta)
    · exact b4_496 theta
    · exact b4_230 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2326 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2325 theta)
    · exact b4_706 theta
    · exact b4_3105 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3048 theta)
    · exact b4_709 theta
    · exact b4_510 theta
    · exact b4_209 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2701 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2825 theta)
    · exact b4_538 theta
    · exact b4_108 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2767 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2818 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3062 theta)
    · exact b4_708 theta
    · exact b4_620 theta
    · exact b4_749 theta
    · exact b4_574 theta
    · exact b4_803 theta
    · exact b4_566 theta
    · exact b4_804 theta
    · exact b4_651 theta
    · exact b4_647 theta
theorem b3_1039 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1039 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1039 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w104 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1040 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1040 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1040 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w105 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1041 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1041 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1041 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w80 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w106 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1042 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1042 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1042 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w80 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons pc1w109 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1043 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1043 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1043 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w112 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1044 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1044 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1044 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w114 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1045 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1045 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1045 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w80 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons pc1w115 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1046 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1046 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1046 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xffff0000,0xff00ff00,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w80 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w117 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1047 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1047 := by
  apply PetersenIndexedNode.close (bank := [s4_413,a4235,a4236,s4_2491,a4237,s4_2761,s4_700,s4_544,a4238,a4239,a4240,a4241,s4_299,a4242,a4243,s4_492,s4_232,a4244,a4245,s4_716,a4246,a4247,s4_721,s4_514,s4_212,a4248,a4249,a4250,s4_115,a4251,a4252,s4_717,a4253,a4254,s4_720,a4255,s4_719,s4_619,s4_807,s4_577,s4_808,s4_567,s4_809,a4256,s4_648]) (PetersenIndexedNode.reasons 256 17 417 0xc4402406310110808c282420231101850484404202120310808a0201080a80010808a0805000280814100a020420208404420270341080884049018614130829c0d0c28250342406084044202901028202400108089080480024041210090104202141010808501448401401090185040280214050a08050142406242009018311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a0810808480c141012010a02848402402120309080480c280a0a080a028280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c04480c0301018098504c4c02101120318980480c6141018080c042505030109404420226221080894144c44210510808180842025040030101809210016120b01141002c2406124840018080c042c2403010180850400e0a07010b0901c14060a1410018080c05002c8015a0c060048838141c0a1012000c8404614120e058500480c6160120318504c2c06141120310702480c150520e04541421018014884045415002a15050840507022101494120e05250050408013941012505002848411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808012a12000c05002603012120107028480428280c080604840441c1210110a0a83824202a101006040302248680c080604480c30b012030921a616024069203006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b004240212080124008d24248404800221012003f001e800e920320038480c8011400860040480c800d92030541500191505084060030210115054006854142101800b884060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d00050180a0e0600080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_413 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_349 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2407 theta)
    · exact b4_2491 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_7 theta)
    · exact b4_2761 theta
    · exact b4_700 theta
    · exact b4_544 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_39 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2318 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_3047 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_443 theta)
    · exact b4_299 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2391 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2522 theta)
    · exact b4_492 theta
    · exact b4_232 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2286 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2283 theta)
    · exact b4_716 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3174 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2550 theta)
    · exact b4_721 theta
    · exact b4_514 theta
    · exact b4_212 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2699 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2826 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_537 theta)
    · exact b4_115 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2645 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2644 theta)
    · exact b4_717 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_3102 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2815 theta)
    · exact b4_720 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_3078 theta)
    · exact b4_719 theta
    · exact b4_619 theta
    · exact b4_807 theta
    · exact b4_577 theta
    · exact b4_808 theta
    · exact b4_567 theta
    · exact b4_809 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_649 theta)
    · exact b4_648 theta
theorem b3_1048 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1048 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1048 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w119 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1049 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1049 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1049 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w121 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
