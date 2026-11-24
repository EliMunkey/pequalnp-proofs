import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S12
import Q1020K12L4S16
import Q1020K12L4S19
import Q1020K12L4S29
import Q1020K12L4S30
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S38
import Q1020K12L4S53
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc3w3 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w2 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w3 stored35 rfl rfl



private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w12 stored35 rfl rfl
private theorem pc3w13 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w14 : PetersenPackedPin.project cycle3 (0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w13 stored34 rfl rfl
private theorem pc3w16 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w15 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w16 stored35 rfl rfl
private theorem pc3w17 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccc00000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 pc3w13 stored33 rfl rfl
private theorem pc3w19 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w18 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w19 stored35 rfl rfl
private theorem pc3w20 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl



private theorem pc2w22 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl

private theorem pc2w25 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl



private theorem pc2w30 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl

private theorem pc3w32 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w13 stored34 rfl rfl
private theorem pc3w33 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc3w35 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w13 stored33 rfl rfl
private theorem pc3w36 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w37 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w3 stored36 rfl rfl
private theorem pc2w38 : PetersenPackedPin.project cycle2 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 stored41 stored42 rfl rfl
private theorem pc2w39 : PetersenPackedPin.project cycle2 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc2w30 stored44 rfl rfl




private theorem pc26w44 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl

private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w44 stored3 rfl rfl



private theorem pc2w50 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc3w51 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w16 stored36 rfl rfl
private theorem pc2w53 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w52 : PetersenPackedPin.project cycle2 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w53 stored45 rfl rfl
private theorem pc3w54 : PetersenPackedPin.project cycle3 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w16 stored37 rfl rfl
private theorem pc3w55 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w19 stored37 rfl rfl
private theorem pc2w57 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored45 rfl rfl
private theorem pc2w58 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored43 stored45 rfl rfl
private theorem pc2w56 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w57 pc2w58 rfl rfl
private theorem pc3w60 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w12 stored33 rfl rfl
private theorem pc3w59 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w60 pc3w9 rfl rfl



private theorem pc111w64 : PetersenPackedPin.project extra111 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored177 stored179 rfl rfl
private theorem pc111w66 : PetersenPackedPin.project extra111 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored178 stored179 rfl rfl
private theorem pc111w63 : PetersenPackedPin.project extra111 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc111w64 pc111w66 rfl rfl




private theorem pc111w73 : PetersenPackedPin.project extra111 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored178 stored183 rfl rfl
private theorem pc111w72 : PetersenPackedPin.project extra111 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc111w73 stored177 rfl rfl
private theorem pc111w74 : PetersenPackedPin.project extra111 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored179 stored183 rfl rfl
private theorem pc111w71 : PetersenPackedPin.project extra111 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc111w72 pc111w74 rfl rfl

private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w16 stored33 rfl rfl
private theorem pc3w76 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w77 pc3w9 rfl rfl
private theorem pc3w78 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w3 pc3w9 rfl rfl
private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl







private theorem pc1w88 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w89 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w87 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w88 pc1w89 rfl rfl








private theorem pc73w98 : PetersenPackedPin.project extra73 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 1 stored129 stored135 rfl rfl
private theorem pc73w100 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w97 : PetersenPackedPin.project extra73 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w98 pc73w100 rfl rfl
private theorem pc73w102 : PetersenPackedPin.project extra73 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w100 stored131 rfl rfl
private theorem pc73w101 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w102 pc73w98 rfl rfl

private theorem pc2w106 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w105 : PetersenPackedPin.project cycle2 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w106 stored43 rfl rfl
private theorem pc2w107 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w104 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc2w105 pc2w107 rfl rfl
private theorem pc2w108 : PetersenPackedPin.project cycle2 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w107 pc2w25 rfl rfl
private theorem pc2w109 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w107 stored43 rfl rfl
private theorem pc1w111 : PetersenPackedPin.project cycle1 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored63 rfl rfl
private theorem pc1w110 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc1w111 stored59 rfl rfl
theorem b3_2814 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2814 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2814 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w2 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2815 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2815 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2815 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2816 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2816 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s3_2816 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccc0000,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w14 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2817 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2817 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2817 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w15 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2818 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2818 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false))] s3_2818 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xc0c0c0c0,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2819 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2819 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2819 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w18 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2820 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2820 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2820 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w20 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2821 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2821 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2821 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w25 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w22 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2822 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2822 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_2822 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w32 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2823 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2823 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2823 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w25 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2824 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2824 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2824 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w33 rfl)))))))))) (by decide +kernel)
theorem b3_2825 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2825 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2825 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w25 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w34 rfl)))))))))) (by decide +kernel)
theorem b3_2826 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2826 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2826 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w35 rfl)))))))))) (by decide +kernel)
theorem b3_2827 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2827 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true))] s3_2827 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w36 rfl)))))))))) (by decide +kernel)
theorem b3_2828 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2828 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2828 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2829 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2829 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,false),(2,false))] s3_2829 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f00000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w39 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w38 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2830 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2830 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_2830 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2831 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2831 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_2831 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w39 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w50 rfl)))))))))) (by decide +kernel)
theorem b3_2832 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2832 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2832 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w51 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2833 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2833 := by
  apply PetersenIndexedNode.close (bank := [s4_2247,a5373,a5374,s4_2847,a5375,a5376,a5377,a5378,a5379,a5380,a5381,a5382,a5383,a5384,a5385,a5386,s4_1402,a5387,a5388,a5389,s4_3176,a5390,s4_2618,a5391,a5392,s4_2603,a5393,a5394,a5395,a5396,s4_512,a5397,a5398,a5399,a5400,a5401,s4_2616,a5402,s4_2617]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108090818c8806101311119100c4444206108088404e0601080884050818a0805004381814100e0604206084044202622210808840484046141308098888c28262222101084044202901828202402108189080480424061210090184206141010818501048401400084045040280014040a08050102101242008404311128200c4044202706010808c444e0c021111080941004202840c1410210118888c8c04202210319180840c62220a08050404808141012000840448402400120209080480821010a0808404280824200a0004202282014000a020504028081080921004202908014100a080a08038301c10242007060283028200a0805040840c030101809203084804204210310900840c480c018080c044c0c0301018088404c4c02101130318980480c2101018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c04921a018080c05081883814184a48690702901a420600c04060242020180908009010424021001080884804202240400c0406030018018080c04420300061080c009a004a280a494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018010c0082003e840c800f2103200490023801121032003a840c31114006cc4444202800d10808c445001c31111080a00324202800c4005c541421018002084060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0804c45000913110180a001006021311400284c44060280038180a000d0005131200c0600080301428680c080604840c41c120c290a1a83824206a103006040302248480c080604420230b0108089212616024049080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c0806050001119108c8a0006232211914000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2247 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1290 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1607 theta)
    · exact b4_2847 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_7 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_707 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_699 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2263 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1434 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1285 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2856 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2319 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1414 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1286 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_3051 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2383 theta)
    · exact b4_1402 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1262 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1258 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1261 theta)
    · exact b4_3176 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2876 theta)
    · exact b4_2618 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_819 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_817 theta)
    · exact b4_2603 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_514 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1275 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_3071 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2601 theta)
    · exact b4_512 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1277 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1274 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1276 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3104 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_3050 theta)
    · exact b4_2616 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2620 theta)
    · exact b4_2617 theta
theorem b3_2834 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2834 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2834 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w52 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2835 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2835 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2835 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w54 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2836 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2836 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2836 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w55 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2837 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2837 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2837 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w30 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w56 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2838 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2838 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2838 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w59 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2839 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2839 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true))] s3_2839 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w59 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w36 rfl)))))))))) (by decide +kernel)
theorem b3_2840 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2840 := by
  intro m le c
  apply rejects_sound extra111 i5 4 tgt small111 hot111 [] s3_2840 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons stored184 (PetersenWireProjection.cons pc111w71 (PetersenWireProjection.cons stored183 (PetersenWireProjection.cons stored182 (PetersenWireProjection.cons stored181 (PetersenWireProjection.cons stored180 (PetersenWireProjection.cons stored179 (PetersenWireProjection.cons pc111w63 (PetersenWireProjection.cons stored178 (PetersenWireProjection.cons stored177 rfl)))))))))) (by decide +kernel)
theorem b3_2841 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2841 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2841 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2842 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2842 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2842 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons pc3w16 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2843 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2843 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2843 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w2 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2844 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2844 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2844 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2845 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2845 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2845 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w20 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2846 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2846 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2846 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w79 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2847 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2847 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2847 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w87 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_2848 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2848 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2848 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2849 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2849 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_2849 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w101 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons pc73w97 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_2850 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2850 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2850 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w104 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2851 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2851 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2851 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w109 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w108 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2852 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2852 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2852 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w109 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w25 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2853 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2853 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(0,true))] s3_2853 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w109 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w106 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2854 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2854 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2854 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w109 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w22 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2855 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2855 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2855 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xffff0000,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w110 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
