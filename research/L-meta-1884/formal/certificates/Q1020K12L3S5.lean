import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S4
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S29
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w8 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w10 stored0 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333333333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000f0f00000f0f0 := PetersenWireProjection.derive 3 pc26w13 pc26w14 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff0000f0f00000f0f00000 := PetersenWireProjection.derive 3 pc26w17 pc26w18 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc26w21 stored1 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfffffffffffffffffffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w19 stored0 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffffffffffffffffafafafafafafafa := PetersenWireProjection.derive 3 pc26w23 stored0 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w29 pc26w30 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xfafafafafafafafaf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w30 stored0 rfl rfl








private theorem pc0w40 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w42 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored51 rfl rfl
private theorem pc0w41 : PetersenPackedPin.project cycle0 (0xcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w40 pc0w42 rfl rfl
private theorem pc0w43 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w44 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl








private theorem pc37w54 : PetersenPackedPin.project extra37 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored65 stored66 rfl rfl
private theorem pc37w53 : PetersenPackedPin.project extra37 (0xffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc37w54 stored67 rfl rfl
private theorem pc37w56 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored66 stored71 rfl rfl
private theorem pc37w55 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc37w56 stored67 rfl rfl








private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w67 stored33 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl








private theorem pc2w77 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w79 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w78 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 1 pc2w79 stored41 rfl rfl
private theorem pc2w80 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc3w81 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 1 pc3w68 stored33 rfl rfl
private theorem pc3w82 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 stored33 stored34 rfl rfl
private theorem pc3w83 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc2w84 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored42 stored43 rfl rfl








private theorem pc74w94 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored113 stored115 rfl rfl
private theorem pc74w93 : PetersenPackedPin.project extra74 (0xffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w94 stored114 rfl rfl
private theorem pc74w96 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored115 stored119 rfl rfl
private theorem pc74w95 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w96 stored113 rfl rfl


private theorem pc34w97 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl






private theorem pc34w106 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w108 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored18 stored22 rfl rfl
private theorem pc34w107 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc34w108 stored16 rfl rfl
private theorem pc34w110 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w109 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff000000000000ffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc34w110 pc34w106 rfl rfl


private theorem pc30w111 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl






private theorem pc30w120 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored10 stored13 rfl rfl
private theorem pc30w122 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w121 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc : BitVec 256) = 0x550055000000000055005500 := PetersenWireProjection.derive 1 pc30w122 stored8 rfl rfl
private theorem pc30w124 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w123 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 pc30w124 pc30w120 rfl rfl
private theorem pc3w125 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w127 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w128 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w126 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333333333333000000003333333300000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w127 pc3w128 rfl rfl
private theorem pc37w129 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl
private theorem pc37w131 : PetersenPackedPin.project extra37 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33333333333333330000000000000000 := PetersenWireProjection.derive 1 stored67 stored71 rfl rfl
private theorem pc37w132 : PetersenPackedPin.project extra37 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33333333333333333333333333333333 := PetersenWireProjection.derive 1 stored66 stored71 rfl rfl
private theorem pc37w130 : PetersenPackedPin.project extra37 (0x3333333333333333333333333333333333333333000000003333333300000000 : BitVec 256) = 0x33333333333333333333333333333333 := PetersenWireProjection.derive 3 pc37w131 pc37w132 rfl rfl
private theorem pc26w134 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w135 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w133 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w134 pc26w135 rfl rfl
private theorem pc26w137 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w136 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w137 stored0 rfl rfl
private theorem pc3w138 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w140 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w141 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w139 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w140 pc3w141 rfl rfl
theorem b3_210 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_210 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true))] s3_210 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_211 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_211 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true))] s3_211 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_212 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_212 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,true),(0,true))] s3_212 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000f0f00000f0f0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_213 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_213 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s3_213 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_214 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_214 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,true))] s3_214 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_215 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_215 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true))] s3_215 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_216 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_216 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(1,false),(0,true))] s3_216 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_217 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_217 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s3_217 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_218 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_218 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s3_218 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_219 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_219 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s3_219 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_220 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_220 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true))] s3_220 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w24 rfl)))))))))) (by decide +kernel)
theorem b3_221 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_221 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(3,true))] s3_221 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w21 rfl)))))))))) (by decide +kernel)
theorem b3_222 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_222 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,true),(0,false))] s3_222 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w25 rfl)))))))))) (by decide +kernel)
theorem b3_223 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_223 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true))] s3_223 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w26 rfl)))))))))) (by decide +kernel)
theorem b3_224 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_224 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(1,true),(0,false))] s3_224 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffafafafafafafafa] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w27 rfl)))))))))) (by decide +kernel)
theorem b3_225 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_225 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s3_225 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_226 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_226 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false)),(false,(0,true),(3,true))] s3_226 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafaf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w31 rfl)))))))))) (by decide +kernel)
theorem b3_227 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_227 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,false))] s3_227 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w41 (PetersenWireProjection.cons pc0w40 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_228 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_228 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_228 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w41 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w43 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_229 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_229 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_229 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w41 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_230 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_230 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(3,true))] s3_230 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons pc0w41 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w44 rfl)))))))))) (by decide +kernel)
theorem b3_231 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_231 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_231 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc37w55 (PetersenWireProjection.cons pc37w53 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 rfl)))))))))) (by decide +kernel)
theorem b3_232 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_232 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_232 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_233 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_233 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_233 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w68 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_234 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_234 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_234 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w78 (PetersenWireProjection.cons pc2w77 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_235 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_235 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_235 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w78 (PetersenWireProjection.cons pc2w77 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w80 rfl)))))))))) (by decide +kernel)
theorem b3_236 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_236 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_236 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xc0c0c0c,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w81 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_237 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_237 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s3_237 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0000,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w82 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_238 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_238 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_238 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_239 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_239 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_239 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w78 (PetersenWireProjection.cons pc2w84 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_240 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_240 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_240 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc74w95 (PetersenWireProjection.cons pc74w93 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl)))))))))) (by decide +kernel)
theorem b3_241 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_241 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_241 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w107 (PetersenWireProjection.cons pc34w106 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w97 rfl)))))))))) (by decide +kernel)
theorem b3_242 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_242 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_242 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xfffffffffffffffff0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w107 (PetersenWireProjection.cons pc34w109 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_243 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_243 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(4,false),(0,false))] s3_243 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x550055000000000055005500,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons pc30w121 (PetersenWireProjection.cons pc30w120 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w111 rfl)))))))))) (by decide +kernel)
theorem b3_244 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_244 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(4,false),(0,false))] s3_244 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x550055000000000055005500,0xffffffffaaaaaaaaffffffffaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w121 (PetersenWireProjection.cons pc30w123 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_245 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_245 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_245 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w125 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_246 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_246 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_246 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfcfcfcfc,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w126 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_247 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_247 := by
  apply PetersenIndexedNode.close (bank := [a4084,a4085,s4_203,s4_198,a4086,a4087,s4_201,a4088,a4089,a4090,s4_200]) (PetersenIndexedNode.reasons 256 17 414 0x184804202610020c058504c200612030a0984808301210120c0540402301510020c054100a20050102820140408301118088c04c4442301310010808c4806200311118900c4444202118088c0524205040490020c052100920049082420124208301282020c04a0209080280010808a0805000280814100a020420248401080866225040198088c04e0c0230119889c18046222301282008c05161228204580a0c05918083014584b230106128301141020c0490102820240010808908048002404121009010420214101080854104840150008c0450402a0015040a08054102301242008c0531102820141014100706038204c440e0c05060504014100a0810c080602430020c05090086004302212010c088301030120c049818060203011080989804202260631300901842020301018084c080602130008c044c4426001302098884c082301030108c04a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180906020302418021811070483004180a0e0906028604018100c0892120302018110808c2c0420224849858090124202018100c08460203021180098104240230011808848046022604018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c0940402624420220c0507028301501020e0540408301131220c04e0602624131210808c4c04202381818980c440420213121080941008381108088c044c4821015040098904c48230141c088c04e0c026241312141006c68263438300d8d06c4850401312098905040262414100a88917122822141022e2450402a2213120a881090062603130018084c4806024240098904c40060231300180842402624109000c0907020302109020e0442400302131200c0a00150009490920c0406020301210100c0484004808212010800840442402101120200602030180044001c54142301018080c06000a030101809410026221301800304c4406225040018080c060006030101808a08016120b01800202c2406122820018080c040c0403010300098880c0806000301018100c042622018080c040604060401800848006020300018100c04060221200302018120005000180000989006020301)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym4 fix4 (by decide +kernel) (b4_1222 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1132 theta)
    · exact b4_203 theta
    · exact b4_198 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_201 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_198 theta)
    · exact b4_201 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1152 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_200 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1152 theta)
    · exact b4_200 theta
theorem b3_248 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_248 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_248 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x33333333333333333333333333333333,0xffff0000ffff0000ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc37w55 (PetersenWireProjection.cons pc37w130 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w129 rfl)))))))))) (by decide +kernel)
theorem b3_249 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_249 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,false))] s3_249 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w136 (PetersenWireProjection.cons pc26w133 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_250 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_250 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_250 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w138 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_251 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_251 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_251 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w139 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
