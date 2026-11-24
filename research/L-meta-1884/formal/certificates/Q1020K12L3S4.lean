import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S56
import Q1020K12L4S58
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S64
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S72
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc30w8 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff0000000000 := PetersenWireProjection.derive 0 stored8 stored14 rfl rfl
private theorem pc30w9 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w7 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00f000f000ff00ff00f000f000 := PetersenWireProjection.derive 3 pc30w8 pc30w9 rfl rfl

private theorem pc30w12 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w11 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w12 stored8 rfl rfl
private theorem pc30w14 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa00000000 := PetersenWireProjection.derive 0 stored8 stored10 rfl rfl
private theorem pc30w15 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0 := PetersenWireProjection.derive 3 pc30w14 pc30w15 rfl rfl
private theorem pc30w16 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w17 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w18 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w19 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w20 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w21 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w22 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w17 stored8 rfl rfl
private theorem pc30w23 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffffffffafafafafffffffffafafafa := PetersenWireProjection.derive 3 pc30w18 stored8 rfl rfl








private theorem pc34w32 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w34 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored17 stored19 rfl rfl
private theorem pc34w33 : PetersenPackedPin.project extra34 (0xffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w34 stored16 rfl rfl
private theorem pc34w35 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w36 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored18 stored22 rfl rfl
private theorem pc34w37 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 1 stored17 stored18 rfl rfl
private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 1 stored16 stored18 rfl rfl
private theorem pc34w39 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 3 pc34w40 pc34w38 rfl rfl
private theorem pc34w41 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w43 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w44 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w42 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc34w43 pc34w44 rfl rfl
private theorem pc34w45 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w46 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w47 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w48 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w46 stored16 rfl rfl
private theorem pc34w49 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl








private theorem pc41w59 : PetersenPackedPin.project extra41 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored90 stored95 rfl rfl
private theorem pc41w58 : PetersenPackedPin.project extra41 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w59 stored91 rfl rfl
private theorem pc41w61 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
private theorem pc41w60 : PetersenPackedPin.project extra41 (0xffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc41w61 pc41w59 rfl rfl




private theorem pc69w64 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl




private theorem pc69w72 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored97 stored98 rfl rfl
private theorem pc69w71 : PetersenPackedPin.project extra69 (0xffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc69w72 pc69w64 rfl rfl


private theorem pc39w73 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl






private theorem pc39w83 : PetersenPackedPin.project extra39 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored75 stored79 rfl rfl
private theorem pc39w82 : PetersenPackedPin.project extra39 (0xffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc39w73 pc39w83 rfl rfl
private theorem pc34w84 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w86 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc34w85 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc34w32 pc34w86 rfl rfl
private theorem pc34w88 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc34w87 : PetersenPackedPin.project extra34 (0xffff0000000000000000 : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 2 pc34w88 pc34w38 rfl rfl


private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl






private theorem pc26w99 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w100 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w98 : PetersenPackedPin.project extra26 (0x888888880000000088888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w99 pc26w100 rfl rfl
private theorem pc26w102 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w101 : PetersenPackedPin.project extra26 (0xaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w99 pc26w102 rfl rfl
private theorem pc26w103 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w100 stored0 rfl rfl
private theorem pc26w105 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w104 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w105 stored0 rfl rfl
private theorem pc26w106 : PetersenPackedPin.project extra26 (0xffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc26w102 stored0 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555555050505050505050 := PetersenWireProjection.derive 1 pc26w89 stored1 rfl rfl
theorem b3_168 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_168 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,true),(4,false))] s3_168 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00f000f000ff00ff00f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w7 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_169 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_169 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(0,true),(1,false))] s3_169 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaa0a0a0a0aaaaaaaaa0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_170 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_170 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true))] s3_170 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w16 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_171 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_171 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true))] s3_171 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w17 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_172 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_172 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(0,true))] s3_172 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_173 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_173 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_173 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_174 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_174 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true))] s3_174 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w19 rfl)))))))))) (by decide +kernel)
theorem b3_175 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_175 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true))] s3_175 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w20 rfl)))))))))) (by decide +kernel)
theorem b3_176 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_176 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(2,true)),(false,(0,true),(3,true))] s3_176 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w21 rfl)))))))))) (by decide +kernel)
theorem b3_177 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_177 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true))] s3_177 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffffff0fff0fffffffffff0fff0] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w22 rfl)))))))))) (by decide +kernel)
theorem b3_178 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_178 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(0,false),(1,true))] s3_178 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffffafafafafffffffffafafafa] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w23 rfl)))))))))) (by decide +kernel)
theorem b3_179 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_179 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(6,true),(3,true))] s3_179 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w19 (PetersenWireProjection.cons pc30w21 rfl)))))))))) (by decide +kernel)
theorem b3_180 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_180 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(3,true),(1,true))] s3_180 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w21 rfl)))))))))) (by decide +kernel)
theorem b3_181 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_181 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s3_181 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons pc34w32 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_182 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_182 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true))] s3_182 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_183 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_183 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true))] s3_183 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons pc34w36 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_184 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_184 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_184 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w37 rfl)))))))))) (by decide +kernel)
theorem b3_185 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_185 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_185 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons pc34w39 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_186 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_186 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s3_186 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w41 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_187 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_187 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,true),(1,false))] s3_187 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w42 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_188 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_188 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s3_188 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w45 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_189 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_189 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s3_189 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w46 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_190 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_190 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true))] s3_190 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w47 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_191 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_191 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [] s3_191 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_192 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_192 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_192 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w37 rfl)))))))))) (by decide +kernel)
theorem b3_193 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_193 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_193 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffaaaaffffaaaa] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w48 rfl)))))))))) (by decide +kernel)
theorem b3_194 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_194 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_194 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons pc34w37 rfl)))))))))) (by decide +kernel)
theorem b3_195 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_195 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_195 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w60 (PetersenWireProjection.cons pc41w58 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 rfl)))))))))) (by decide +kernel)
theorem b3_196 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_196 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_196 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w71 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w64 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_197 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_197 := by
  apply PetersenIndexedNode.close (bank := [s4_49,s4_46,s4_2478,s4_2486,s4_97,a4065,a4066,s4_2792,s4_126,a4067,a4068,a4069,a4070,s4_40,a4071,a4072,s4_141,s4_26,a4073,a4074,s4_154,s4_3035,a4075,s4_159,a4076,s4_19,a4077,a4078,s4_3,a4079,a4080,a4081,s4_156,a4082,s4_157,s4_151,a4083]) (PetersenIndexedNode.reasons 256 17 420 0x622212021880884046141210118888c2824222210109010840470300a82940008404504028001c0c0a0807030210105414840480118a828c202480830a0984060048614130a092020541448084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a0205040280812021210048081d0d1410074142a0a38300a82874347060150d0a828a0802a0a46060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050101505121005404614114100a80854142820150518504908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c04060232a2818080c042a0a131109808ca8a262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406028010898910602840441c0a0c060044838141c0a10104c48840461410989084004808212010801850442402120120204c48480815051090054146141131209890541426241405185048480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c1210110a0a83824202a101006040302248480c080604480830b012020921261602404920200604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c08868203020181098904240212080104007d24248404800e21012003d001d2101120220038420215054006842026141800c884045415001b15051850600306141800a4004e00245040800894102002f0016800a9410200205040141040038504048408006921005041000f141012102001848400301400280c0484808004a12000c05000b0301212020010848013124001806024240800280c044c49000713121090200084240018140008060461608000985800605000301811858200006160)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_49 theta
    · exact b4_46 theta
    · exact b4_2478 theta
    · exact b4_2486 theta
    · exact b4_97 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2723 theta)
    · exact b4_2792 theta
    · exact b4_126 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_40 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2455 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2489 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_126 theta)
    · exact b4_40 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2455 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2489 theta)
    · exact b4_141 theta
    · exact b4_26 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2374 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2373 theta)
    · exact b4_154 theta
    · exact b4_3035 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2540 theta)
    · exact b4_159 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_97 theta)
    · exact b4_19 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2723 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2792 theta)
    · exact b4_3 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2819 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_156 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2819 theta)
    · exact b4_156 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_151 theta)
    · exact b4_157 theta
    · exact b4_151 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_157 theta)
theorem b3_198 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_198 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_198 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w82 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w73 rfl)))))))))) (by decide +kernel)
theorem b3_199 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_199 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_199 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w85 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w84 rfl)))))))))) (by decide +kernel)
theorem b3_200 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_200 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true)),(false,(5,false),(0,false))] s3_200 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w87 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w84 rfl)))))))))) (by decide +kernel)
theorem b3_201 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_201 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s3_201 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w98 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w89 rfl)))))))))) (by decide +kernel)
theorem b3_202 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_202 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s3_202 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w101 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w89 rfl)))))))))) (by decide +kernel)
theorem b3_203 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_203 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,false))] s3_203 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w103 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_204 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_204 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_204 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w106 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_205 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_205 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_205 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w107 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_206 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_206 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true))] s3_206 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w108 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_207 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_207 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true))] s3_207 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x55550000555500005555000055550000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w109 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_208 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_208 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(1,true),(0,true))] s3_208 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x55555555555555555050505050505050,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_209 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_209 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true))] s3_209 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons pc26w100 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
