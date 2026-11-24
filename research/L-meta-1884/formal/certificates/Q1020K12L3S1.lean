import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc32w0 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl






private theorem pc32w10 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc32w11 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 stored25 stored26 rfl rfl
private theorem pc32w9 : PetersenPackedPin.project extra32 (0xff00ff00000000 : BitVec 256) = 0xf0f00000f0f0000000000000000 := PetersenWireProjection.derive 2 pc32w10 pc32w11 rfl rfl


private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl






private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0x4444444444444444 : BitVec 256) = 0x5050000050500000505000005050000 := PetersenWireProjection.derive 2 pc26w22 pc26w23 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0x8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w25 pc26w23 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xcccccccccccccccc : BitVec 256) = 0x5050000050500000505000005050000 := PetersenWireProjection.derive 1 pc26w23 stored0 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w28 stored0 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 3 pc26w34 pc26w32 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w36 pc26w37 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xfafa0000fafa0000fafa0000fafa0000 := PetersenWireProjection.derive 3 pc26w40 pc26w41 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w43 stored0 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl


private theorem pc30w47 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl






private theorem pc30w57 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w58 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w56 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w57 pc30w58 rfl rfl
private theorem pc32w60 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w61 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored25 stored28 rfl rfl
private theorem pc32w59 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w60 pc32w61 rfl rfl


private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl






private theorem pc34w72 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w73 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored17 stored19 rfl rfl
private theorem pc34w71 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w72 pc34w73 rfl rfl








private theorem pc2w82 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl
private theorem pc2w84 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored42 stored43 rfl rfl
private theorem pc2w83 : PetersenPackedPin.project cycle2 (0xcccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w82 pc2w84 rfl rfl
private theorem pc2w85 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w86 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w87 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w58 stored8 rfl rfl
private theorem pc30w90 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xcccccccccccccccc : BitVec 256) = 0xf000f00000000000f000f00 := PetersenWireProjection.derive 1 pc30w90 stored8 rfl rfl
private theorem pc32w91 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc32w61 stored24 rfl rfl
private theorem pc32w93 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored25 stored29 rfl rfl
private theorem pc32w92 : PetersenPackedPin.project extra32 (0xcccccccccccccccc : BitVec 256) = 0xa0a00000a0a00000a0a00000a0a := PetersenWireProjection.derive 1 pc32w93 stored24 rfl rfl
private theorem pc34w94 : PetersenPackedPin.project extra34 (0xffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w73 stored16 rfl rfl
private theorem pc34w96 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored17 stored22 rfl rfl
private theorem pc34w95 : PetersenPackedPin.project extra34 (0xcccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa := PetersenWireProjection.derive 1 pc34w96 stored16 rfl rfl








private theorem pc39w106 : PetersenPackedPin.project extra39 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored74 stored75 rfl rfl
private theorem pc39w105 : PetersenPackedPin.project extra39 (0xffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc39w106 stored73 rfl rfl
private theorem pc39w108 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored74 stored79 rfl rfl
private theorem pc39w107 : PetersenPackedPin.project extra39 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc39w108 stored73 rfl rfl








private theorem pc3w117 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w118 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w119 stored33 rfl rfl
private theorem pc3w120 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w121 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 stored33 stored35 rfl rfl








private theorem pc0w130 : PetersenPackedPin.project cycle0 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored49 stored50 rfl rfl
private theorem pc0w132 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w131 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 pc0w132 stored49 rfl rfl
private theorem pc0w133 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc3w135 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w134 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 1 pc3w135 stored33 rfl rfl
private theorem pc3w136 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 stored34 stored35 rfl rfl








private theorem pc1w145 : PetersenPackedPin.project cycle1 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored58 rfl rfl
private theorem pc1w147 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 stored58 stored63 rfl rfl
private theorem pc1w146 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 1 pc1w147 stored57 rfl rfl
private theorem pc1w148 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl
theorem b3_42 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_42 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(0,false),(7,false))] s3_42 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w9 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w0 rfl)))))))))) (by decide +kernel)
theorem b3_43 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_43 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false))] s3_43 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x5050000050500000505000005050000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_44 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_44 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s3_44 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_45 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_45 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false))] s3_45 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x5050000050500000505000005050000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_46 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_46 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_46 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_47 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_47 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_47 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w30 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_48 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_48 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true))] s3_48 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_49 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_49 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_49 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_50 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_50 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_50 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafafafafafa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_51 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_51 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_51 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w35 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_52 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_52 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_52 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons pc26w35 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_53 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_53 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s3_53 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_54 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_54 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,true),(5,false))] s3_54 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xfafa0000fafa0000fafa0000fafa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_55 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_55 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s3_55 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w42 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_56 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_56 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(4,true))] s3_56 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_57 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_57 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true))] s3_57 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_58 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_58 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s3_58 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_59 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_59 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true))] s3_59 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_60 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_60 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true))] s3_60 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffafafffffafafffffafafffffafa] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w45 rfl)))))))))) (by decide +kernel)
theorem b3_61 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_61 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_61 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_62 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_62 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true))] s3_62 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w56 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w47 rfl)))))))))) (by decide +kernel)
theorem b3_63 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_63 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true))] s3_63 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w59 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w0 rfl)))))))))) (by decide +kernel)
theorem b3_64 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_64 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_64 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w71 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w62 rfl)))))))))) (by decide +kernel)
theorem b3_65 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_65 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_65 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons pc2w82 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_66 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_66 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_66 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons pc2w85 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_67 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_67 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_67 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w86 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_68 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_68 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_68 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_69 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_69 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_69 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w87 rfl)))))))))) (by decide +kernel)
theorem b3_70 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_70 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false))] s3_70 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf000f00000000000f000f00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w89 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_71 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_71 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false))] s3_71 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a00000a0a00000a0a00000a0a,0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w92 (PetersenWireProjection.cons pc32w91 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_72 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_72 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_72 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons pc34w94 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_73 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_73 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_73 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w107 (PetersenWireProjection.cons pc39w105 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 rfl)))))))))) (by decide +kernel)
theorem b3_74 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_74 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_74 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w117 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_75 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_75 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_75 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w117 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w120 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_76 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_76 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_76 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xc0c0c0c,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w121 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_77 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_77 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,false))] s3_77 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w131 (PetersenWireProjection.cons pc0w130 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_78 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_78 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,false))] s3_78 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w131 (PetersenWireProjection.cons pc0w130 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w133 rfl)))))))))) (by decide +kernel)
theorem b3_79 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_79 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,false))] s3_79 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0000,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w134 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_80 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_80 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_80 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w119 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_81 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_81 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true))] s3_81 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccc,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons pc3w136 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_82 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_82 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_82 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w146 (PetersenWireProjection.cons pc1w145 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_83 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_83 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_83 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0] (PetersenWireProjection.cons pc1w146 (PetersenWireProjection.cons pc1w145 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w148 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
