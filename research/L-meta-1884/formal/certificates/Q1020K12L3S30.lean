import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S12
import Q1020K12L4S19
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S30
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc30w3 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffffffffff0000ffffffffffff0000 := PetersenWireProjection.derive 3 stored8 stored15 rfl rfl

private theorem pc30w5 : PetersenPackedPin.project extra30 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored10 stored15 rfl rfl
private theorem pc30w2 : PetersenPackedPin.project extra30 (0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffaaaaffff0000ffffaaaaffff0000 := PetersenWireProjection.derive 0 pc30w3 pc30w5 rfl rfl




private theorem pc30w11 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored9 stored15 rfl rfl
private theorem pc30w12 : PetersenPackedPin.project extra30 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xfffff0f0ffff0000fffff0f0ffff0000 := PetersenWireProjection.derive 0 pc30w3 pc30w13 rfl rfl






private theorem pc19w20 : PetersenPackedPin.project tree19 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored139 stored142 rfl rfl

private theorem pc19w19 : PetersenPackedPin.project tree19 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc19w20 stored143 rfl rfl

private theorem pc19w24 : PetersenPackedPin.project tree19 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc19w19 stored137 rfl rfl






private theorem pc3w31 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w30 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w31 stored38 rfl rfl

private theorem pc3w35 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w30 stored33 rfl rfl




private theorem pc16w40 : PetersenPackedPin.project tree16 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored147 stored148 rfl rfl

private theorem pc16w39 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc16w40 stored149 rfl rfl



private theorem pc16w48 : PetersenPackedPin.project tree16 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored149 stored148 rfl rfl
private theorem pc16w47 : PetersenPackedPin.project tree16 (0xffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccc0000cccc := PetersenWireProjection.derive 1 pc16w48 stored145 rfl rfl
private theorem pc16w49 : PetersenPackedPin.project tree16 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored147 stored149 rfl rfl
private theorem pc16w46 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc16w47 pc16w49 rfl rfl




private theorem pc34w54 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl

private theorem pc34w53 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w54 stored19 rfl rfl



private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w61 stored16 rfl rfl








private theorem pc2w70 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w72 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w71 : PetersenPackedPin.project cycle2 (0xffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w70 pc2w72 rfl rfl








private theorem pc41w82 : PetersenPackedPin.project extra41 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored89 stored95 rfl rfl
private theorem pc41w81 : PetersenPackedPin.project extra41 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w82 stored91 rfl rfl
private theorem pc41w84 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored90 rfl rfl
private theorem pc41w83 : PetersenPackedPin.project extra41 (0xffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc41w84 pc41w82 rfl rfl
private theorem pc2w86 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w85 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 1 pc2w86 stored41 rfl rfl
private theorem pc2w87 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored41 stored43 rfl rfl
private theorem pc2w88 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 2 stored42 stored47 rfl rfl
private theorem pc34w89 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w90 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored17 stored22 rfl rfl
private theorem pc34w91 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl








private theorem pc32w99 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored28 stored29 rfl rfl
private theorem pc32w101 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored25 stored29 rfl rfl
private theorem pc32w102 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl







private theorem pc0w109 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w112 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w113 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc3w114 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w115 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 stored33 stored35 rfl rfl
private theorem pc2w116 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w118 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w119 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc34w120 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc2w121 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 3 pc2w70 pc2w88 rfl rfl
private theorem pc2w122 : PetersenPackedPin.project cycle2 (0xffffffffcccccccc0000000000000000ffffffffcccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 1 pc2w86 stored42 rfl rfl
private theorem pc2w123 : PetersenPackedPin.project cycle2 (0xffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 pc2w116 stored42 rfl rfl








private theorem pc1w132 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w134 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 stored59 stored63 rfl rfl
private theorem pc1w131 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w132 pc1w134 rfl rfl
private theorem pc1w135 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 stored57 stored59 rfl rfl
private theorem pc2w136 : PetersenPackedPin.project cycle2 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 1 pc2w72 stored43 rfl rfl
private theorem pc2w137 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc1w138 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc1w139 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored59 rfl rfl
private theorem pc2w141 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored41 stored47 rfl rfl
private theorem pc2w140 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 1 pc2w141 stored43 rfl rfl
private theorem pc41w142 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl
private theorem pc41w143 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc41w142 stored90 rfl rfl
private theorem pc34w144 : PetersenPackedPin.project extra34 (0xcccc0000cccc00000000000000000000cccc0000cccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc34w89 stored17 rfl rfl
private theorem pc34w145 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w146 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w147 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w148 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w149 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w150 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
theorem b3_1260 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1260 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,false)),(false,(5,true),(0,true))] s3_1260 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffff0000ffffaaaaffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w2 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1261 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1261 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(2,false)),(false,(0,true),(5,true))] s3_1261 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0ffff0000fffff0f0ffff0000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w11 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w12 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1262 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1262 := by
  intro m le c
  apply rejects_sound tree19 i6 6 tgt small19 hot19 [] s3_1262 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0x0,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc,0xff00ff00ff00ff00] (PetersenWireProjection.cons pc19w24 (PetersenWireProjection.cons stored144 (PetersenWireProjection.cons stored142 (PetersenWireProjection.cons pc19w19 (PetersenWireProjection.cons stored141 (PetersenWireProjection.cons stored140 (PetersenWireProjection.cons stored139 (PetersenWireProjection.cons stored138 (PetersenWireProjection.cons stored137 rfl))))))))) (by decide +kernel)
theorem b3_1263 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1263 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1263 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w35 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w30 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1264 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1264 := by
  intro m le c
  apply rejects_sound tree16 i6 6 tgt small16 hot16 [] s3_1264 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] (PetersenWireProjection.cons pc16w46 (PetersenWireProjection.cons stored152 (PetersenWireProjection.cons stored148 (PetersenWireProjection.cons stored151 (PetersenWireProjection.cons stored150 (PetersenWireProjection.cons pc16w39 (PetersenWireProjection.cons stored147 (PetersenWireProjection.cons stored146 (PetersenWireProjection.cons stored145 rfl))))))))) (by decide +kernel)
theorem b3_1265 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1265 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s3_1265 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1266 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1266 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1266 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w71 (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1267 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1267 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1267 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w83 (PetersenWireProjection.cons pc41w81 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 rfl)))))))))) (by decide +kernel)
theorem b3_1268 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1268 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1268 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w71 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w72 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1269 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1269 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1269 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w71 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1270 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1270 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1270 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w85 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1271 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1271 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1271 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w84 (PetersenWireProjection.cons pc41w81 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 rfl)))))))))) (by decide +kernel)
theorem b3_1272 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1272 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,true))] s3_1272 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa,0xf0f0f0f0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w88 (PetersenWireProjection.cons pc2w87 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 rfl)))))))))) (by decide +kernel)
theorem b3_1273 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1273 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,false),(5,true))] s3_1273 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaa0000aaaa0000aaaa0000aaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w90 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1274 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1274 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(1,false),(5,true))] s3_1274 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xaaaa0000aaaa0000aaaa0000aaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w102 (PetersenWireProjection.cons pc32w101 (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1275 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1275 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1275 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xcccccccc,0xaaaaaaaa,0x0,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w113 (PetersenWireProjection.cons pc0w112 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w109 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1276 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1276 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1276 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w115 (PetersenWireProjection.cons pc3w114 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1277 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1277 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,true))] s3_1277 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w88 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w116 rfl)))))))))) (by decide +kernel)
theorem b3_1278 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1278 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true)),(false,(1,false),(6,true))] s3_1278 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xf000f000f000f000f000f000f000f00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w119 (PetersenWireProjection.cons pc30w118 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w117 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1279 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1279 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(4,true)),(false,(3,false),(7,true))] s3_1279 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaa0000aaaa0000aaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w90 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w120 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1280 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1280 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,true))] s3_1280 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w121 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1281 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1281 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,true))] s3_1281 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w122 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1282 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1282 := by
  apply PetersenIndexedNode.close (bank := [s4_64,a4371,a4372,a4373]) (PetersenIndexedNode.reasons 256 17 173 0xc4046202311109010a202504024848e060480838181202124049202490914100a0005000280812020a080706038301410134249212490d2484890004800240414040908028201410121005040382014180a0800c0486026222018080c0448082406018080c0426221311018080c0416020309018080c040e020305018092424c2404809240488400420021201202084806260313010900848050404841109005444282015110a0800c04464003011090006048302622280c0806044808240480c0806042120109000c0806041302018900c0806040b02018500c0806040602109200c084240030201810848108088404490931110840442025040383014100e0c04840141012100504015110a080544428200301313000c04c4c0018080c050702424001810848006042120511124848e060480838181202042022101383014100e0c05040141012100504048401311018084c440602313010900c4c04240109000c084240030280014000600070000)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_64 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_528 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_830 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1280 theta)
theorem b3_1283 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1283 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,false))] s3_1283 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w123 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1284 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1284 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,false))] s3_1284 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w123 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w116 rfl)))))))))) (by decide +kernel)
theorem b3_1285 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1285 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1285 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w135 (PetersenWireProjection.cons pc1w131 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1286 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1286 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1286 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffaaaa,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w136 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1287 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1287 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_1287 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w87 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w137 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 rfl)))))))))) (by decide +kernel)
theorem b3_1288 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1288 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1288 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w87 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w86 (PetersenWireProjection.cons stored42 rfl)))))))))) (by decide +kernel)
theorem b3_1289 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1289 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1289 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w87 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w72 rfl)))))))))) (by decide +kernel)
theorem b3_1290 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1290 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1290 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc] (PetersenWireProjection.cons pc1w135 (PetersenWireProjection.cons pc1w139 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w138 rfl)))))))))) (by decide +kernel)
theorem b3_1291 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1291 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1291 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafa,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w70 (PetersenWireProjection.cons pc2w140 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1292 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1292 := by
  apply PetersenIndexedNode.close (bank := [a4374,s4_920,a4375,a4376,a4377,s4_918,a4378,s4_954,a4379,a4380,a4381,s4_956]) (PetersenIndexedNode.reasons 256 17 420 0x702010809c000a000614128001c080c2825020280008404a0005808141016000a00048402800160209080500828000a080a000280824200a0004202282014000a02050402808108092100420254040a0815000a0006460280015010c8c05004280005040a00024040a0809000420224201200090104840240410808504042024c440a080504050401c180e08131103830141814100504028205202018094800a000424028001480884805002280000c04a0002606018080c0442026260108089818c4c02406108080c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406024909098914400a00041c0a8001242483814809280004c48a00021010989084044808313012020840462602101120204c4848084941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260508080c094200a00041c128001420283825000a80000604a000248480c080604420230b010808921261602404908080604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c09070203020181098904240212049094002d0808a0005040280012424a0805101280020014a000210128200840448087060120208404e0c0210112021410048084840282012100504080041410121010009484014101410050406460282014100282054440a0819180a88854400a081410028200301282000c0426228003098880c0500070301098894100262241c0a820006022624514100c050702a282514009891410026240181282000604212050c0884800604a181018108481410021208002c00114040a0001080a8000c4442101108090808c2826101311118504c4444202108088404e0c021011080941006222310138300c44442225040108088404504021011400121005010280014100a020501048401080884044c4421011080818084a0a2501131109414420a06021080884044c4821011080a0e060004230113124000c4c48838110808840442402808108000c084202210010900840442020302140400c0a0003000015052820042022101)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym2 fix2 (by decide +kernel) (b4_1037 theta)
    · exact b4_920 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_89 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1083 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1093 theta)
    · exact b4_918 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_362 theta)
    · exact b4_954 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_335 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_955 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_907 theta)
    · exact b4_956 theta
theorem b3_1293 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1293 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1293 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w84 (PetersenWireProjection.cons pc41w143 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w142 rfl)))))))))) (by decide +kernel)
theorem b3_1294 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1294 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,false),(1,false))] s3_1294 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w144 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1295 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1295 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(5,true))] s3_1295 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w145 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1296 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1296 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_1296 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w146 rfl)))))))))) (by decide +kernel)
theorem b3_1297 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1297 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,false),(1,false))] s3_1297 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w148 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w147 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1298 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1298 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(1,true))] s3_1298 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w148 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w145 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1299 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1299 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_1299 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w148 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w146 rfl)))))))))) (by decide +kernel)
theorem b3_1300 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1300 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_1300 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w148 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w149 rfl)))))))))) (by decide +kernel)
theorem b3_1301 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1301 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_1301 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons pc34w150 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w149 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
