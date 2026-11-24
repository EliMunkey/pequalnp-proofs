import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S5
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S14
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S62
import Q1020K12L4S64
import Q1020K12L4S66
import Q1020K12L4S70
import Q1020K12L4S73
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc0w3 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w5 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w2 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w3 pc0w5 rfl rfl
private theorem pc0w7 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl




private theorem pc0w12 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl




private theorem pc2w15 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w18 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored42 stored43 rfl rfl




private theorem pc2w23 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl




private theorem pc1w26 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w29 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc1w34 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc2w35 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w23 stored43 rfl rfl




private theorem pc3w38 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w42 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w41 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w42 stored35 rfl rfl




private theorem pc1w48 : PetersenPackedPin.project cycle1 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored63 rfl rfl
private theorem pc1w47 : PetersenPackedPin.project cycle1 (0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc1w48 stored59 rfl rfl




private theorem pc26w51 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl

private theorem pc26w54 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl



private theorem pc26w59 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl




private theorem pc69w62 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w65 : PetersenPackedPin.project extra69 (0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w62 stored98 rfl rfl




private theorem pc69w70 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored97 stored100 rfl rfl
private theorem pc1w71 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w26 stored57 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccc33333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w73 pc3w74 rfl rfl
private theorem pc1w76 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc1w75 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc1w76 pc1w26 rfl rfl
private theorem pc1w78 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w77 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc1w78 stored59 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w79 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w80 stored2 rfl rfl




private theorem pc30w83 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl

private theorem pc30w86 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl



private theorem pc30w91 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w92 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w93 stored10 rfl rfl




private theorem pc32w96 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl

private theorem pc32w99 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl



private theorem pc32w104 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w106 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w105 : PetersenPackedPin.project extra32 (0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w106 stored26 rfl rfl




private theorem pc34w109 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl

private theorem pc34w112 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl



private theorem pc34w117 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w119 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w118 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc34w119 stored18 rfl rfl
private theorem pc1w120 : PetersenPackedPin.project cycle1 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored58 rfl rfl
private theorem pc3w121 : PetersenPackedPin.project cycle3 (0xffffffffffffffff000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc3w42 stored34 rfl rfl
private theorem pc3w122 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w42 stored34 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc3w124 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc30w125 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w126 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w127 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl



private theorem pc117w129 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored122 stored123 rfl rfl

private theorem pc117w132 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored123 stored124 rfl rfl




private theorem pc117w138 : PetersenPackedPin.project extra117 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 stored121 stored124 rfl rfl
private theorem pc117w139 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc117w132 stored122 rfl rfl
private theorem pc26w140 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc3w141 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc30w142 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc32w143 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc34w144 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl


private theorem pc116w145 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored107 rfl rfl


private theorem pc116w149 : PetersenPackedPin.project extra116 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored107 stored111 rfl rfl




private theorem pc116w155 : PetersenPackedPin.project extra116 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored105 stored111 rfl rfl
private theorem pc116w156 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc116w149 stored105 rfl rfl
private theorem pc116w157 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored106 rfl rfl
theorem b3_1092 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1092 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s3_1092 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0xf0f0f0f0,0x0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w12 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w7 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w2 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1093 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1093 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1093 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w23 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w18 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w15 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1094 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1094 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1094 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xffffcccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w29 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w26 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1095 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1095 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1095 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w23 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w35 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w15 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1096 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1096 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1096 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w41 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1097 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1097 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1097 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w47 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1098 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1098 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1098 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1099 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1099 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1099 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w70 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w65 (PetersenWireProjection.cons pc69w62 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1100 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1100 := by
  apply PetersenIndexedNode.close (bank := [a4296,s4_2495,s4_304,a4297,s4_235,s4_754,a4298,a4299,s4_801,s4_519,a4300,a4301,s4_770,a4302,a4303,a4304,s4_773,s4_629,s4_781,s4_583,s4_782,s4_565,s4_778,s4_555,s4_788,s4_769,a4305]) (PetersenIndexedNode.reasons 256 17 420 0x622210808840484046141210118888c282422221010840442027030400690602840441c0a0c05c0c0838170302101200328404210120e04840448086160120208404c2c021011202107024808501008405400084045040280014040a0805010210104202210131110840442024202800b90808c445001821111080842022101800a884044202838115050a82a002c2a0a150520e04420221014808141012000840448402400120209080480821010a0808404280824200a0004202282014000a020504028081080921004202800994100a080838138301c18200287060383020e04a08050401888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840424040a08090004202242012000901048402404108085040420245c48a0805040838115110a88917122a22151120e04504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0442026260108089818c4c02406108080c0406028008a12010900838103010180a00240602030120e05090084801282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030241c0884804240c2c0018100c0907020302018130b0042402120108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030280084003d242484043130210108405000e210112020c4c04808210118980840448088006920220019000b0180a0e04c4c00301150540028541421013130084045414626015050840600122101800298980c4c0504080021410200110007800314100c4c050401511189805444282080010a0805445000315110a080c4c028200301189800c0484803332199800c046664030121200c4c062600181189800604212080000848006050001018108480c4c02120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_347 theta)
    · exact b4_2495 theta
    · exact b4_304 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2520 theta)
    · exact b4_235 theta
    · exact b4_754 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3104 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2548 theta)
    · exact b4_801 theta
    · exact b4_519 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2697 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2795 theta)
    · exact b4_770 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_535 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2642 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2964 theta)
    · exact b4_773 theta
    · exact b4_629 theta
    · exact b4_781 theta
    · exact b4_583 theta
    · exact b4_782 theta
    · exact b4_565 theta
    · exact b4_778 theta
    · exact b4_555 theta
    · exact b4_788 theta
    · exact b4_769 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_216 theta)
theorem b3_1101 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1101 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1101 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xffffcccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w71 (PetersenWireProjection.cons pc1w26 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1102 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1102 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1102 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w71 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1103 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1103 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1103 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w72 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1104 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1104 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1104 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w72 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1105 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1105 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1105 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xcccccccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w75 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1106 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1106 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1106 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1107 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1107 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1107 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1108 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1108 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1108 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1109 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1109 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1109 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons pc30w92 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1110 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1110 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1110 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons pc32w96 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1111 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1111 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1111 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons pc32w105 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1112 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1112 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1112 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w117 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w112 (PetersenWireProjection.cons pc34w109 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1113 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1113 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1113 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w117 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w112 (PetersenWireProjection.cons pc34w118 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1114 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1114 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s3_1114 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xffffcccc,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w26 (PetersenWireProjection.cons pc1w120 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1115 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1115 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1115 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons pc3w121 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1116 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1116 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1116 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w122 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1117 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1117 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1117 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w123 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1118 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1118 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1118 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w124 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1119 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1119 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1119 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w125 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1120 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1120 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1120 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w126 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1121 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1121 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1121 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w117 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w112 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w127 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1122 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1122 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1122 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccc,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w138 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons pc117w132 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w129 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1123 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1123 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1123 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccc,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w138 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons pc117w132 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w139 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1124 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1124 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1124 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1125 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1125 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_1125 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w140 rfl)))))))))) (by decide +kernel)
theorem b3_1126 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1126 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1126 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w141 rfl)))))))))) (by decide +kernel)
theorem b3_1127 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1127 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(4,true),(1,true))] s3_1127 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w142 rfl)))))))))) (by decide +kernel)
theorem b3_1128 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1128 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_1128 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w143 rfl)))))))))) (by decide +kernel)
theorem b3_1129 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1129 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_1129 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w117 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w112 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w144 rfl)))))))))) (by decide +kernel)
theorem b3_1130 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1130 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1130 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc116w155 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w149 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 (PetersenWireProjection.cons pc116w145 rfl)))))))))) (by decide +kernel)
theorem b3_1131 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1131 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1131 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc116w155 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w149 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 (PetersenWireProjection.cons pc116w156 rfl)))))))))) (by decide +kernel)
theorem b3_1132 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1132 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1132 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc116w155 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w149 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 (PetersenWireProjection.cons pc116w157 rfl)))))))))) (by decide +kernel)
theorem b3_1133 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1133 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1133 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w141 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
