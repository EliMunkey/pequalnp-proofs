import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w9 pc26w10 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w12 stored0 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0x22222222000000002222222200000000222222220000000022222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w17 stored2 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000222222220000000022222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w16 pc26w14 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w20 stored2 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w19 pc26w21 rfl rfl







private theorem pc30w29 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl

private theorem pc30w32 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w31 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaa00000000ffaaffaa := PetersenWireProjection.derive 1 pc30w32 stored8 rfl rfl







private theorem pc32w40 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl

private theorem pc32w43 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc32w42 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w43 stored24 rfl rfl







private theorem pc34w51 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl

private theorem pc34w54 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w53 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc34w54 stored16 rfl rfl







private theorem pc2w62 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl

private theorem pc2w65 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w64 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 1 pc2w65 stored41 rfl rfl




private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl



private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w76 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 1 pc3w68 stored33 rfl rfl
private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl







private theorem pc1w85 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl

private theorem pc1w88 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w87 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 1 pc1w88 stored57 rfl rfl







private theorem pc69w96 : PetersenPackedPin.project extra69 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored97 stored100 rfl rfl
private theorem pc69w98 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w95 : PetersenPackedPin.project extra69 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc69w96 pc69w98 rfl rfl

private theorem pc69w100 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w98 stored97 rfl rfl
private theorem pc30w101 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored12 stored13 rfl rfl
private theorem pc30w102 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w103 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w104 : PetersenPackedPin.project extra30 (0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w32 stored13 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w106 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0x3030303030303030303030303030303030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored13 stored14 rfl rfl
private theorem pc30w108 : PetersenPackedPin.project extra30 (0x30303030000000003030303000000000303030300000000030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w109 stored10 rfl rfl
private theorem pc30w107 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000303030300000000030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w108 pc30w106 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w112 stored10 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaa00000000ffaaffaa := PetersenWireProjection.derive 1 pc30w111 pc30w113 rfl rfl
private theorem pc26w114 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl
private theorem pc32w115 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored27 stored28 rfl rfl
private theorem pc32w116 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored26 stored28 rfl rfl
private theorem pc32w117 : PetersenPackedPin.project extra32 (0xff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w43 stored28 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored25 stored28 rfl rfl
private theorem pc32w119 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w122 : PetersenPackedPin.project extra32 (0x3300330033003300330033003300330033003300330033003300330033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored28 stored29 rfl rfl
private theorem pc32w121 : PetersenPackedPin.project extra32 (0x33003300000000003300330000000000330033000000000033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc32w122 stored26 rfl rfl
private theorem pc32w120 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000330033000000000033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w121 pc32w119 rfl rfl
private theorem pc32w125 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w124 : PetersenPackedPin.project extra32 (0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w125 stored26 rfl rfl
private theorem pc32w126 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored28 rfl rfl
private theorem pc32w123 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ffffffffffccffccffffffffffccffcc : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w124 pc32w126 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl
private theorem pc30w128 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl
private theorem pc34w129 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored18 stored19 rfl rfl
private theorem pc34w130 : PetersenPackedPin.project extra34 (0xffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w54 stored19 rfl rfl
private theorem pc34w131 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored17 stored19 rfl rfl
private theorem pc34w132 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored16 stored19 rfl rfl
private theorem pc34w135 : PetersenPackedPin.project extra34 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored19 stored22 rfl rfl
private theorem pc34w134 : PetersenPackedPin.project extra34 (0x33330000000000003333000000000000333300000000000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w135 stored18 rfl rfl
private theorem pc34w133 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000333300000000000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w134 pc34w132 rfl rfl
theorem b3_1512 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1512 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1512 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1513 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1513 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1513 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1514 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1514 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1514 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1515 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1515 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1515 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1516 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1516 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1516 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1517 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1517 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1517 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1518 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1518 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1518 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1519 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1519 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1519 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w29 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1520 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1520 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1520 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1521 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1521 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1521 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1522 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1522 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1522 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w64 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w62 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1523 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1523 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1523 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w68 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1524 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1524 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1524 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w64 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w62 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w65 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1525 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1525 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1525 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w77 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1526 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1526 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,true),(1,true))] s3_1526 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffcccc,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w87 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w85 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1527 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1527 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1527 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w100 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w95 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_1528 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1528 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1528 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1529 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1529 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1529 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w101 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1530 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1530 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1530 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1531 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1531 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1531 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w103 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1532 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1532 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1532 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w104 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1533 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1533 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1533 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1534 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1534 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1534 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w106 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1535 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1535 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1535 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w107 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1536 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1536 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1536 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffaaffaa00000000ffaaffaa,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w110 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1537 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1537 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1537 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w114 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1538 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1538 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1538 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w112 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1539 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1539 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1539 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w115 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1540 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1540 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1540 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w116 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1541 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1541 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1541 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w117 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1542 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1542 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1542 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w118 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1543 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1543 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1543 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w119 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1544 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1544 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1544 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1545 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1545 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1545 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w123 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1546 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1546 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1546 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1547 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1547 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1547 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w125 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1548 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1548 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1548 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w31 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w128 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1549 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1549 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1549 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w129 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1550 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1550 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1550 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w130 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1551 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1551 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1551 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w131 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1552 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1552 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1552 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w132 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1553 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1553 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_1553 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w133 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
