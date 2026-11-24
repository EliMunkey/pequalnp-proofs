import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S13
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S54
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc34w5 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w4 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc34w5 stored18 rfl rfl
private theorem pc34w8 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w3 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc34w4 pc34w8 rfl rfl



private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc34w13 stored16 rfl rfl





private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl



private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w24 stored0 rfl rfl





private theorem pc30w28 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl



private theorem pc30w35 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w34 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaa00000000ffaaffaa := PetersenWireProjection.derive 1 pc30w35 stored8 rfl rfl





private theorem pc32w39 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl



private theorem pc32w46 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc32w45 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w46 stored24 rfl rfl



private theorem pc2w50 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored42 stored43 rfl rfl





private theorem pc2w57 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w56 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 1 pc2w57 stored41 rfl rfl



private theorem pc1w61 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl





private theorem pc1w68 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w67 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 1 pc1w68 stored57 rfl rfl



private theorem pc69w72 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored97 stored100 rfl rfl

private theorem pc69w71 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w72 stored99 rfl rfl




private theorem pc69w80 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w79 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w80 stored97 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc69w82 : PetersenPackedPin.project extra69 (0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w80 stored98 rfl rfl
private theorem pc1w83 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w68 stored57 rfl rfl


private theorem pc29w84 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl


private theorem pc29w88 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl




private theorem pc29w94 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f := PetersenWireProjection.derive 1 pc29w88 stored153 rfl rfl


private theorem pc37w95 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl


private theorem pc37w99 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl




private theorem pc37w105 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc37w99 stored67 rfl rfl
private theorem pc29w106 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w88 stored153 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w108 stored2 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w111 stored10 rfl rfl
private theorem pc32w112 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w114 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w113 : PetersenPackedPin.project extra32 (0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w114 stored26 rfl rfl
private theorem pc34w115 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc1w116 : PetersenPackedPin.project cycle1 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored58 rfl rfl




private theorem pc117w121 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored123 stored124 rfl rfl
private theorem pc117w120 : PetersenPackedPin.project extra117 (0x33333333000000000000000000000000333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc117w121 stored122 rfl rfl
private theorem pc117w124 : PetersenPackedPin.project extra117 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored121 stored122 rfl rfl
private theorem pc117w119 : PetersenPackedPin.project extra117 (0xffffffffffffffff000000000000000000000000333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc117w120 pc117w124 rfl rfl




private theorem pc117w129 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc117w121 stored121 rfl rfl
private theorem pc117w131 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc117w121 stored122 rfl rfl
private theorem pc117w132 : PetersenPackedPin.project extra117 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored121 stored122 rfl rfl
private theorem pc117w130 : PetersenPackedPin.project extra117 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc117w131 pc117w132 rfl rfl
private theorem pc26w133 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc30w134 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w135 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w136 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc117w137 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored122 stored123 rfl rfl
private theorem pc26w138 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl


private theorem pc41w139 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl






private theorem pc41w149 : PetersenPackedPin.project extra41 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored90 stored95 rfl rfl
private theorem pc41w148 : PetersenPackedPin.project extra41 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w149 stored91 rfl rfl
private theorem pc30w150 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc32w151 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc34w152 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc41w153 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl
private theorem pc41w154 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w149 stored91 rfl rfl
private theorem pc41w155 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
theorem b3_1554 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1554 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1554 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfafafafafafafafa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w3 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1555 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1555 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1555 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1556 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1556 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1556 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w5 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1557 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1557 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1557 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w28 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1558 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1558 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1558 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w39 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1559 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1559 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1559 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w56 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w50 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1560 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1560 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,true),(1,true))] s3_1560 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffcccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w67 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1561 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1561 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1561 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w79 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w71 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1562 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1562 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1562 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w81 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1563 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1563 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1563 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w79 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w82 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1564 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1564 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,true),(1,true))] s3_1564 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffcccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w67 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w83 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1565 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1565 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1565 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1566 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1566 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1566 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w94 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w88 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w84 rfl)))))))))) (by decide +kernel)
theorem b3_1567 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1567 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_1567 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc37w105 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons pc37w99 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w95 rfl)))))))))) (by decide +kernel)
theorem b3_1568 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1568 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1568 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w94 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w88 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w106 rfl)))))))))) (by decide +kernel)
theorem b3_1569 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1569 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1569 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w107 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1570 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1570 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1570 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w109 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1571 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1571 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1571 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w110 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1572 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1572 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1572 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w112 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1573 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1573 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1573 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w113 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1574 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1574 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1574 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w115 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1575 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1575 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1575 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w4 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1576 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1576 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,true),(1,true))] s3_1576 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffcccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w67 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w116 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1577 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1577 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1577 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0x0,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons pc117w129 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons pc117w119 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1578 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1578 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1578 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w129 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w130 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1579 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1579 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1579 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w133 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1580 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1580 := by
  apply PetersenIndexedNode.close (bank := [s4_1014,a4065,a4616,s4_2912]) (PetersenIndexedNode.reasons 256 17 173 0xc44442023111108084202420231110840448082101280014000a08042022820054142a0a5040188088404422221012400120009010420224200a08050404840148088404421221010e82854142a1a1505230110808840c42020a08054442a221410128088404420a21010a80854042a0a24200a08070402830141021001080084040301212000c0406024240018088404c4c00301018084c0406220301018082c0406120301018081c04060a0301309010808c2c04202098904c48420231301c0c854146260150510980c4c050404941141005444282015110a0800c04666003011898006048404420280c08424003020181084800604420230b000c0806042302109000c0806041302018900c0806040b02018500c0806040602109200c08424003020181084812424840480014000600070000210130a088404c2821080884045414a080383014100e0c05040141012100504048400301212000c048480212010900c4c0c2c0018120e0806048382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_1014 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2784 theta)
    · exact b4_2912 theta
theorem b3_1581 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1581 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1581 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w134 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1582 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1582 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1582 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w135 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1583 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1583 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1583 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w136 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1584 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1584 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1584 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w129 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w137 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1585 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1585 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1585 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w129 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w131 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1586 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1586 := by
  apply PetersenIndexedNode.close (bank := [s4_441,a4617,a4618,s4_2512,s4_704,a4516,a4339,s4_2799,s4_863,a4619,a4620,a4621,a4622,s4_337,a4623,a4624,a4625,s4_257,a4626,a4627,s4_960,s4_204,a4527,a4350,a4546,s4_155,a4547,a4079,s4_3,a4628,s4_1095,a4629,s4_1092,s4_1046,s4_1099,a4630,s4_1093]) (PetersenIndexedNode.reasons 256 17 426 0x18888420221012101185048404622230a090888840421011080a00462a0a5000210114100a00080122820141008404150521010c4442a0a310110809c180420231113830084444202150510809202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a0204202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a8291818282046022101191808404460632301081884041410210109010282024001080890804800240412100901042021410108085414484015012820050402a0215050a0805414a08024201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180898180602030110809898042022606313009018420203010180a0042060203010a8284c4426028011098880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a003e26244180a101107028301801020e050702840413122101084042624210112020c4c0480821011898084044808131212020541483811505282004c4826241505098905014a08041c08a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0462600301212004c4826200301098900c0484803130189810a0a0302018121011070484044282a0e09080a8404018100c0892120302018110808c2c0420224849858090124202018100c094302030201810a8284240230250c08848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c09070221201090098900604030241c080c0806042624109008482003d001d4909210120038840421014006884044808800c920208405001b210112022003048081505400584202a080800a88404541500171505282020028a080383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848400301400280c0484808004a12000c05000b0301212020010848013124001806028381800280c044c490007131220e0600088381018140008060483828000a0e0806050003018120e0a00008382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_441 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_383 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2396 theta)
    · exact b4_2512 theta
    · exact b4_704 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2799 theta
    · exact b4_863 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_281 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2289 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2571 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_454 theta)
    · exact b4_337 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2386 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2531 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_867 theta)
    · exact b4_257 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2269 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2574 theta)
    · exact b4_960 theta
    · exact b4_204 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2668 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2824 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_546 theta)
    · exact b4_155 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2624 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2819 theta)
    · exact b4_3 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2918 theta)
    · exact b4_1095 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_661 theta)
    · exact b4_1092 theta
    · exact b4_1046 theta
    · exact b4_1099 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_917 theta)
    · exact b4_1093 theta
theorem b3_1587 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1587 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1587 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w138 rfl)))))))))) (by decide +kernel)
theorem b3_1588 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1588 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1588 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w148 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w139 rfl)))))))))) (by decide +kernel)
theorem b3_1589 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1589 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1589 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w34 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w150 rfl)))))))))) (by decide +kernel)
theorem b3_1590 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1590 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1590 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w151 rfl)))))))))) (by decide +kernel)
theorem b3_1591 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1591 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1591 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w152 rfl)))))))))) (by decide +kernel)
theorem b3_1592 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1592 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1592 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w148 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w153 rfl)))))))))) (by decide +kernel)
theorem b3_1593 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1593 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1593 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w148 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w154 rfl)))))))))) (by decide +kernel)
theorem b3_1594 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1594 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1594 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w148 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w155 rfl)))))))))) (by decide +kernel)
theorem b3_1595 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1595 := by
  apply PetersenIndexedNode.close (bank := [a4631,s4_2513,s4_705,a4632,s4_1079,s4_1108,a4633,a4634,s4_157,a4635,s4_2925,a4636,s4_1091,s4_1095,s4_1044,s4_1111,s4_1038,s4_1112,a4637,s4_1117,a4638,a4629,s4_1047,s4_1100,s4_1084,s4_1053,s4_1088,a4639,s4_1033]) (PetersenIndexedNode.reasons 256 17 426 0x18888480862022101084044202622210808840484042404210120039001b5000210105414a00080068a82854148404800d21010c4442a0a310110809c180420231113830084444202150510809202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a0204202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a829181828204602210105444840446060a889081884041410210109010282024001080890804800240412100901042021410108085414484015012820050402a0215050a0805414a08024201210131102820141014100706038204c440e0c05060504014100a081080900194200240400c0484004202018080c049010800c2404098180602030110809898042022606313009018420203010180a002c060203010a8284c442602800b898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a002b00144180a101107028301210120e04840448086160120208404c2c021011202107024808150520e045414a080800928200541500131505282010702a080494120e05250050408008141012505001148411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808007212000c05000f030121201070284804282884810a088404018100c090a0a030201812101042408404248480c080604420230b010808921261602404908080604030250c080c0806042a0a109008c094302212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b004240212080064002e00148404490921012001a92124909210120004840421012484884044808800412020840500092101120212424c2021505248484202a0805111084045414a2225101282012424a20238302888944445040490924848e0c0921249011410144449202141024849242448404d0d2486850409a1a4d0912101242492120301248480c0484808003212000c0500070301212012424860280024000d2024838149092404a000a9212490920e060004838101812484806048382800000e0806050001018120e0924248302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_385 theta)
    · exact b4_2513 theta
    · exact b4_705 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2614 theta)
    · exact b4_1079 theta
    · exact b4_1108 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_282 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2572 theta)
    · exact b4_157 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2820 theta)
    · exact b4_2925 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2897 theta)
    · exact b4_1091 theta
    · exact b4_1095 theta
    · exact b4_1044 theta
    · exact b4_1111 theta
    · exact b4_1038 theta
    · exact b4_1112 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_572 theta)
    · exact b4_1117 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_662 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_661 theta)
    · exact b4_1047 theta
    · exact b4_1100 theta
    · exact b4_1084 theta
    · exact b4_1053 theta
    · exact b4_1088 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1034 theta)
    · exact b4_1033 theta
end Orbits1020Cost12
