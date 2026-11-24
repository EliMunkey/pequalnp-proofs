import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S5
import Q1020K12L4S12
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S26
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S39
import Q1020K12L4S40
import Q1020K12L4S46
import Q1020K12L4S54
import Q1020K12L4S56
import Q1020K12L4S64
import Q1020K12L4S66
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S71
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc32w0 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl





private theorem pc32w8 : PetersenPackedPin.project extra32 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored24 stored29 rfl rfl
private theorem pc32w10 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc32w7 : PetersenPackedPin.project extra32 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xafafafafafafafafaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 pc32w8 pc32w10 rfl rfl



private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl





private theorem pc34w20 : PetersenPackedPin.project extra34 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 1 stored16 stored22 rfl rfl
private theorem pc34w22 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w19 : PetersenPackedPin.project extra34 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaafafafafafafafafa := PetersenWireProjection.derive 2 pc34w20 pc34w22 rfl rfl



private theorem pc2w24 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl





private theorem pc2w32 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w31 : PetersenPackedPin.project cycle2 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w32 pc2w34 rfl rfl



private theorem pc29w37 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl

private theorem pc29w36 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w37 stored153 rfl rfl




private theorem pc29w46 : PetersenPackedPin.project extra29 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored153 stored154 rfl rfl
private theorem pc29w45 : PetersenPackedPin.project extra29 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc29w46 pc29w37 rfl rfl





private theorem pc30w50 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl



private theorem pc30w56 : PetersenPackedPin.project extra30 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff00000000 := PetersenWireProjection.derive 1 stored8 stored14 rfl rfl
private theorem pc30w58 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w55 : PetersenPackedPin.project extra30 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xff00ff00ffaaffaaff00ff00ffaaffaa := PetersenWireProjection.derive 2 pc30w56 pc30w58 rfl rfl









private theorem pc26w66 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w71 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w69 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 2 pc26w70 pc26w71 rfl rfl
private theorem pc26w73 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 3 pc26w73 pc26w66 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl
private theorem pc30w75 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w77 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w76 : PetersenPackedPin.project extra30 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xff00ff00fff0fff0ff00ff00fff0fff0 := PetersenWireProjection.derive 2 pc30w56 pc30w77 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 2 stored8 stored9 rfl rfl
private theorem pc30w78 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00fff0fff0ff00ff00fff0fff0 := PetersenWireProjection.derive 3 pc30w79 pc30w75 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl
private theorem pc32w81 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w83 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w82 : PetersenPackedPin.project extra32 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xafafaaaaafafaaaaafafaaaaafafaaaa := PetersenWireProjection.derive 2 pc32w8 pc32w83 rfl rfl
private theorem pc32w85 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored24 stored25 rfl rfl
private theorem pc32w84 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffffffffffffffffffccffccffccffcc : BitVec 256) = 0xafafaaaaafafaaaaafafaaaaafafaaaa := PetersenWireProjection.derive 3 pc32w85 pc32w81 rfl rfl
private theorem pc30w86 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl
private theorem pc34w88 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w90 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w89 : PetersenPackedPin.project extra34 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 2 pc34w20 pc34w90 rfl rfl
private theorem pc34w92 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored16 stored17 rfl rfl
private theorem pc34w91 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffffffffffffffffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w92 pc34w88 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc32w94 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl
private theorem pc26w95 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc29w97 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl
private theorem pc29w96 : PetersenPackedPin.project extra29 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc29w46 pc29w97 rfl rfl
private theorem pc29w99 : PetersenPackedPin.project extra29 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored153 stored155 rfl rfl
private theorem pc29w98 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w99 pc29w37 rfl rfl
private theorem pc32w100 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc34w101 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc26w102 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl



private theorem pc0w104 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl




private theorem pc0w112 : PetersenPackedPin.project cycle0 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33003300 := PetersenWireProjection.derive 1 stored49 stored55 rfl rfl
private theorem pc0w111 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w112 pc0w104 rfl rfl

private theorem pc30w114 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w115 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w116 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc0w117 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl
private theorem pc26w118 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc29w119 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc30w120 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc0w121 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc29w122 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w97 stored153 rfl rfl
theorem b3_3024 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3024 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(0,true),(1,true))] s3_3024 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafafafafafafafaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w7 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w0 rfl)))))))))) (by decide +kernel)
theorem b3_3025 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3025 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(0,true),(1,true))] s3_3025 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaafafafafafafafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w19 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w12 rfl)))))))))) (by decide +kernel)
theorem b3_3026 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3026 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3026 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w31 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w24 rfl)))))))))) (by decide +kernel)
theorem b3_3027 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3027 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3027 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w45 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w36 rfl)))))))))) (by decide +kernel)
theorem b3_3028 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3028 := by
  apply PetersenIndexedNode.close (bank := [s4_2274,a5686,a5687,a5688,s4_2797,s4_155,a5689,s4_2926,a5690,s4_1933]) (PetersenIndexedNode.reasons 256 17 173 0x84044202108088404c4446141211105414a08050400a8285414e04050400a8285414e08050600a82a00125040282040020a080d0404840141012100504028202420074142a0a150d0a8285040484024200a0805040c84024600a0805040484024200a08054042a021505121005040382014180a0800c0484804240018080c04c4406222018080c04c4804260018080c0426020311018080c0416020309018080c040e0203050180a000d00058003c00120006c4447030311118504c88861413222042022101150528200e0c05040383014100504048401410121000c0484800301212004c4862603130098904c48c4448001098904c4862603130098905414262414050a0284c483624131a098905440282014110a0800c04262003011898006020301018118580c2c00302018131111888a0302018118580c2c00302018108c0842400302018104c0806240302018102c080614030201810180842480302800080c0806050000109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2274 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1720 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2991 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact b4_2797 theta
    · exact b4_155 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_830 theta)
    · exact b4_2926 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2355 theta)
    · exact b4_1933 theta
theorem b3_3029 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3029 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(0,true),(4,true))] s3_3029 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ffaaffaaff00ff00ffaaffaa,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w55 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w50 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3030 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3030 := by
  apply PetersenIndexedNode.close (bank := [a5691,s4_2813,a5692,s4_2808,a5693,s4_2877,s4_1529,a5694,a5695,a5696,a5688,a5697,a5698,s4_2809,s4_1649,s4_2810,a5699,s4_1934,a5700,s4_2811,a5701,a5702]) (PetersenIndexedNode.reasons 256 17 420 0x800ac00518808840421412101140402101500021010c282a0005010185054040840410808840600242101108090a08c2826141800998504c282428210808840520210011480021010a080900048081410120208404800821012001c9080484010a08a0805040800794100a080428248402420062225040188088404e0c0210118889c1804222210128200840518182820460221010908084044606121010818840414102101191102820141010a08908048406444121009080428214100a080501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a00180602030110a098980c4808006b1301098042820301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a0017000a490921011888884042141400250888c8886222211108504c4446222322220010c88830a0b1110c2822101703008404c282e06070200840588882101282031110a0809080800324200a08100072820242018888d0402420311109080282080020a0809081000524200a08188882820434138181c0c006026222018090d04c444622001809c0c00602800100c04060284042120210120006424048092101006020301214100c040602c8882120109008504424021203222006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800000c040602c4442120109020002424021203111006020301428280c080604840430b0210110a0a61604202a10100604030264c480c080604428230b0185819312616030b010a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030262a280c080604c44430b0311118a8a616062a2311100604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_101 theta)
    · exact b4_2813 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1115 theta)
    · exact b4_2808 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1539 theta)
    · exact b4_2877 theta
    · exact b4_1529 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2882 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2698 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_520 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_776 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1491 theta)
    · exact b4_2809 theta
    · exact b4_1649 theta
    · exact b4_2810 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2364 theta)
    · exact b4_1934 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_787 theta)
    · exact b4_2811 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_765 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_764 theta)
theorem b3_3031 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3031 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3031 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons pc26w66 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3032 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3032 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3032 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons pc26w72 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3033 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3033 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3033 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3034 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3034 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3034 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3035 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3035 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3035 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xff00ff00fff0fff0ff00ff00fff0fff0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w78 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3036 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3036 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3036 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3037 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3037 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3037 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w81 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3038 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3038 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3038 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w84 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3039 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3039 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3039 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3040 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3040 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3040 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3041 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3041 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_3041 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3042 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3042 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_3042 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3043 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3043 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3043 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w93 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3044 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3044 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3044 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w94 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3045 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3045 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3045 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w95 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3046 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3046 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3046 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w37 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3047 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3047 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3047 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w98 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3048 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3048 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3048 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w50 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3049 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3049 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3049 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w100 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3050 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3050 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_3050 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w101 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3051 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3051 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3051 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w102 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3052 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3052 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3052 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w111 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w104 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_3053 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3053 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3053 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3054 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3054 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3054 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w115 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3055 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3055 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_3055 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w116 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3056 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3056 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3056 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xffff0000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w111 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w117 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_3057 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3057 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3057 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w111 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3058 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3058 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_3058 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w118 rfl)))))))))) (by decide +kernel)
theorem b3_3059 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3059 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3059 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w119 rfl)))))))))) (by decide +kernel)
theorem b3_3060 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3060 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3060 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w120 rfl)))))))))) (by decide +kernel)
theorem b3_3061 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3061 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_3061 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w0 rfl)))))))))) (by decide +kernel)
theorem b3_3062 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3062 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_3062 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w12 rfl)))))))))) (by decide +kernel)
theorem b3_3063 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3063 := by
  apply PetersenIndexedNode.close (bank := [s4_2796,s4_222,a5703,s4_2926]) (PetersenIndexedNode.reasons 256 17 173 0x8404420210808c44462222101108094040c2822101084044202a020504021090c4444202311110808a08070603830141016040a020501828080a4044202210910808a0807060383014100908028201410121005040a02064600a08094044202210510808908028201410121005040382014180a0800c0426221311018080c04a0205012018080c0442024260018080c0426221311018080c0416020309018080c040e0203050180a000500018001c00014444a020511128080840448082101322214504a080514128200a08090802820242005444282015110a0800c048480030121200848062603130109014444a0205111280808404424021011202884806260313010900848050404941109005444282015110a0800c044640030110900060203010181084804240030201812808107040302018110808c2c0030201810848042400302018104c0806240302018102c080614030201810180842480302109000c0806042120109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_2796 theta
    · exact b4_222 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_836 theta)
    · exact b4_2926 theta
theorem b3_3064 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3064 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3064 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w111 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w121 rfl)))))))))) (by decide +kernel)
theorem b3_3065 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3065 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3065 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w122 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
