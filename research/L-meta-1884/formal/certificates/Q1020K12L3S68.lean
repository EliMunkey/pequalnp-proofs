import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S2
import Q1020K12L4S4
import Q1020K12L4S12
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S24
import Q1020K12L4S29
import Q1020K12L4S30
import Q1020K12L4S31
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S39
import Q1020K12L4S53
import Q1020K12L4S54
import Q1020K12L4S57
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S74
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc2w2 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl



private theorem pc2w9 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w8 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w9 stored43 rfl rfl




private theorem pc18w14 : PetersenPackedPin.project tree18 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored186 stored187 rfl rfl

private theorem pc18w16 : PetersenPackedPin.project tree18 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored188 stored187 rfl rfl
private theorem pc18w13 : PetersenPackedPin.project tree18 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w14 pc18w16 rfl rfl



private theorem pc18w23 : PetersenPackedPin.project tree18 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000 := PetersenWireProjection.derive 0 stored188 stored191 rfl rfl
private theorem pc18w22 : PetersenPackedPin.project tree18 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w23 stored186 rfl rfl
private theorem pc18w24 : PetersenPackedPin.project tree18 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored187 stored191 rfl rfl
private theorem pc18w21 : PetersenPackedPin.project tree18 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c0ccccccccc0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc18w22 pc18w24 rfl rfl




private theorem pc1w29 : PetersenPackedPin.project cycle1 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored62 rfl rfl

private theorem pc1w31 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored62 rfl rfl
private theorem pc1w28 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w29 pc1w31 rfl rfl



private theorem pc1w38 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w37 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w38 stored57 rfl rfl
private theorem pc1w39 : PetersenPackedPin.project cycle1 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored62 stored63 rfl rfl
private theorem pc1w36 : PetersenPackedPin.project cycle1 (0xccccccccc0c0c0c0ccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc1w37 pc1w39 rfl rfl

private theorem pc2w42 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored45 rfl rfl
private theorem pc2w43 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored43 stored45 rfl rfl
private theorem pc2w41 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w42 pc2w43 rfl rfl
private theorem pc2w46 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w45 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w46 stored41 rfl rfl
private theorem pc2w47 : PetersenPackedPin.project cycle2 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored45 stored47 rfl rfl
private theorem pc2w44 : PetersenPackedPin.project cycle2 (0xcccccccccc00cc00cccccccccc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc2w45 pc2w47 rfl rfl




private theorem pc34w52 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc34w51 : PetersenPackedPin.project extra34 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w52 stored19 rfl rfl


private theorem pc34w58 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w52 pc34w58 rfl rfl








private theorem pc0w67 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w69 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc0w68 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w69 pc0w67 rfl rfl

private theorem pc0w72 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w71 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 3 pc0w72 pc0w67 rfl rfl







private theorem pc3w81 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w82 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w81 pc3w82 rfl rfl
private theorem pc3w83 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w86 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w87 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w85 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 pc3w86 pc3w87 rfl rfl
private theorem pc0w89 : PetersenPackedPin.project cycle0 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33003300 := PetersenWireProjection.derive 1 stored49 stored55 rfl rfl
private theorem pc0w90 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w88 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w89 pc0w90 rfl rfl
private theorem pc0w92 : PetersenPackedPin.project cycle0 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored55 rfl rfl
private theorem pc0w93 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w91 : PetersenPackedPin.project cycle0 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 2 pc0w92 pc0w93 rfl rfl
private theorem pc3w94 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w95 : PetersenPackedPin.project cycle3 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w94 stored35 rfl rfl
private theorem pc1w96 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl
private theorem pc1w97 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc0w98 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w67 stored49 rfl rfl
private theorem pc0w99 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc2w100 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc2w101 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored41 stored43 rfl rfl
private theorem pc2w102 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w104 stored35 rfl rfl
private theorem pc0w106 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w105 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc0w106 stored51 rfl rfl
private theorem pc0w108 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored51 rfl rfl
private theorem pc0w107 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 1 pc0w69 pc0w108 rfl rfl



private theorem pc26w112 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl

private theorem pc26w114 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 pc26w112 pc26w114 rfl rfl




private theorem pc26w120 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc0w121 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w90 pc0w93 rfl rfl
private theorem pc0w122 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w99 pc0w67 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w120 stored2 rfl rfl
private theorem pc3w125 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w124 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 pc3w125 pc3w87 rfl rfl
private theorem pc3w126 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w81 stored35 rfl rfl
private theorem pc0w127 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc0w93 stored50 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w114 stored0 rfl rfl
private theorem pc0w129 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc0w69 pc0w67 rfl rfl
private theorem pc3w130 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w87 stored33 rfl rfl
private theorem pc26w131 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w132 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w120 stored0 rfl rfl
private theorem pc0w133 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc0w134 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored49 stored55 rfl rfl
private theorem pc3w135 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w104 stored34 rfl rfl
private theorem pc3w136 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w82 stored34 rfl rfl
theorem b3_2856 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2856 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2856 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w8 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w2 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2857 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2857 := by
  apply PetersenIndexedNode.close (bank := [s4_2249,a5403,a5404,s4_2848,s4_2626,a4664,a5405,s4_2812,a5406,a5407,a5408,a5409,a5410,a5411,a5412,a5413,a5414,s4_1404,a5415,a5416,s4_2639,a4107,a5417,a5418,a5419,a5420,a5421,a5422,a4835,a5423,a5424,a5425,a5426,s4_2649,a5427,s4_2648,a5428,s4_2647]) (PetersenIndexedNode.reasons 256 17 432 0x8012188898404840461413080a004ac282614121010c4448404501008405400084045040280014040a080501021010420221013111084044202c28230a098504c4446141211130a08420221014808141012000840448402400120209080480821010a0808404391924200e4446222282018888e4645040311918889210062221888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840464440a0805040622224201888991104840242018888504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406028011018080c04622262601888a0046c4c04260188880c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301311100c040602c888212010900c444424031113222006020301801000c04060221013130084060042626014050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c0406040301212000602030151114007944448404800ea10114445001f511121012003884043111400688404c282800c90808c445001b311130a0a0030c28230a0c005854142101800a88404c283001730a08840600282101282040048a08090808008a4200a0810013282024202002090801511400385444282080068a0805445000f15110a082001828201311400284c4406028004818084c45000b13110180a001006022120400184c480301800280c0484810007212000c0600080301428280c080604840441c120c090a0a83824202a10100604030264c480c080604622230b0188899312616030b01888806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c0806050001119108c8a0006232211914000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2249 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1267 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1670 theta)
    · exact b4_2848 theta
    · exact b4_2626 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_525 theta)
    · exact b4_2812 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2309 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1532 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1264 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2863 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2293 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1540 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1265 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2859 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2400 theta)
    · exact b4_1404 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1252 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2879 theta)
    · exact b4_2639 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_204 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_543 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2824 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2608 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_505 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1268 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2886 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2599 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1014 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1272 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2916 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_741 theta)
    · exact b4_2649 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1486 theta)
    · exact b4_2648 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_763 theta)
    · exact b4_2647 theta
theorem b3_2858 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2858 := by
  intro m le c
  apply rejects_sound tree18 i6 6 tgt small18 hot18 [] s3_2858 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored192 (PetersenWireProjection.cons pc18w21 (PetersenWireProjection.cons stored191 (PetersenWireProjection.cons stored190 (PetersenWireProjection.cons stored189 (PetersenWireProjection.cons stored188 (PetersenWireProjection.cons pc18w13 (PetersenWireProjection.cons stored186 (PetersenWireProjection.cons stored185 rfl))))))))) (by decide +kernel)
theorem b3_2859 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2859 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2859 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w36 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w28 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_2860 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2860 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2860 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w44 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w41 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2861 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2861 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s3_2861 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2862 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2862 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2862 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2863 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2863 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2863 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2864 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2864 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(3,true))] s3_2864 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w69 rfl)))))))))) (by decide +kernel)
theorem b3_2865 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2865 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_2865 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xff0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons pc0w71 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2866 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2866 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2866 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2867 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2867 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_2867 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2868 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2868 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2868 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w88 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2869 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2869 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(1,true))] s3_2869 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xffffcccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w91 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2870 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2870 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s3_2870 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccc0000,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w95 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w94 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2871 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2871 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,false))] s3_2871 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w97 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w96 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_2872 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2872 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s3_2872 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xff000000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w99 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w98 rfl)))))))))) (by decide +kernel)
theorem b3_2873 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2873 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_2873 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w102 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w101 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w100 rfl)))))))))) (by decide +kernel)
theorem b3_2874 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2874 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2874 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w103 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2875 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2875 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_2875 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffffcccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w105 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2876 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2876 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s3_2876 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffffff00,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w107 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2877 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2877 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(5,false),(1,false))] s3_2877 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f00000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w111 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2878 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2878 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2878 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w121 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2879 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2879 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s3_2879 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w122 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2880 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2880 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s3_2880 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w123 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2881 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2881 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false))] s3_2881 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xc0c0c0c0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w124 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2882 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2882 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2882 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w126 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2883 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2883 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(1,true))] s3_2883 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffffcccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w93 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2884 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2884 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2884 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w87 (PetersenWireProjection.cons pc3w94 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2885 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2885 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2885 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w90 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2886 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2886 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_2886 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xffffcccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w127 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2887 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2887 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2887 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2888 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2888 := by
  apply PetersenIndexedNode.close (bank := [a5429,a5430,a5431,a5432,a5433,a4509,a5434,s4_3134,a5435,a4447,a5436,s4_2970,s4_2666,s4_192,a5437,a4565]) (PetersenIndexedNode.reasons 256 17 170 0x10808840424041c0c0e060480824042808140c048081080884054040a08042121c0c090107030240414100e0c0706028202c0814040a030501014000a0005010240414100e0c070602820121005040282024200a0814040c8c0141012000900048082808121005040282024200a080704028301410018084c4426220301018094040a0240301018089010480c0301018084c4426220301018082c0406120301018081c04060a030100c044c482624018080c054040a022018080c049010480a0180898904c480301018084c0406220301018082c04061203010300018000c040301800740036001f000c8005280820016a02021011080a0010a0808004a8202000c50408003941020008282080028a082000406028001818088480030101810848042400302018128081070403020181120209012030201810848042400302018104c0806240302018102c080614030201810180842480302018000c000602060401814000200020302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b4_1323 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3134 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1323 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_3134 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1323 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3134 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1323 theta)
    · exact b4_3134 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1344 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2970 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1344 theta)
    · exact b4_2970 theta
    · exact b4_2666 theta
    · exact b4_192 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1360 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2917 theta)
theorem b3_2889 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2889 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(7,true),(3,true))] s3_2889 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w128 rfl)))))))))) (by decide +kernel)
theorem b3_2890 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2890 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(3,true))] s3_2890 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w129 rfl)))))))))) (by decide +kernel)
theorem b3_2891 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2891 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2891 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w130 rfl)))))))))) (by decide +kernel)
theorem b3_2892 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2892 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(7,true),(3,true))] s3_2892 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w112 (PetersenWireProjection.cons pc26w131 rfl)))))))))) (by decide +kernel)
theorem b3_2893 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2893 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true))] s3_2893 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w132 rfl))))))))) (by decide +kernel)
theorem b3_2894 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2894 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s3_2894 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w98 (PetersenWireProjection.cons pc0w69 rfl)))))))))) (by decide +kernel)
theorem b3_2895 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2895 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s3_2895 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xffccffcc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w67 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w134 (PetersenWireProjection.cons pc0w133 rfl)))))))))) (by decide +kernel)
theorem b3_2896 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2896 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2896 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w135 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2897 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2897 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2897 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w136 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
