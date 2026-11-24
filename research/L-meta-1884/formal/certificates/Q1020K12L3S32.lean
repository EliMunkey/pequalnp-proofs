import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S21
import Q1020K12L4S62
import Q1020K12L4S67
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc2w8 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w7 : PetersenPackedPin.project cycle2 (0xcccccccc00000000ffffffff00000000cccccccc00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w8 stored43 rfl rfl

private theorem pc2w10 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl







private theorem pc0w19 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w18 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w19 stored49 rfl rfl

private theorem pc0w21 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w22 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc000000000000000000000000cccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w21 pc0w19 rfl rfl



private theorem pc1w25 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc1w31 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl

private theorem pc1w33 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 stored57 stored59 rfl rfl
private theorem pc0w34 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w19 stored49 rfl rfl
private theorem pc2w35 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc2w36 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl



private theorem pc3w38 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl




private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w47 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 stored33 stored35 rfl rfl
private theorem pc0w48 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w19 stored51 rfl rfl




private theorem pc30w51 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl



private theorem pc30w57 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl

private theorem pc30w59 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc0w60 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w19 stored52 rfl rfl
private theorem pc0w61 : PetersenPackedPin.project cycle0 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w19 stored53 rfl rfl
private theorem pc2w62 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w10 pc2w36 rfl rfl
private theorem pc1w63 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w64 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w66 pc3w67 rfl rfl
private theorem pc2w68 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored41 stored47 rfl rfl
private theorem pc2w70 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0 := PetersenWireProjection.derive 0 stored41 stored47 rfl rfl
private theorem pc2w71 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w69 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w70 pc2w71 rfl rfl
private theorem pc2w73 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w72 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0 := PetersenWireProjection.derive 3 pc2w70 pc2w73 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w66 pc3w45 rfl rfl







private theorem pc26w82 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w82 pc26w84 rfl rfl

private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc2w88 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w87 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w8 pc2w88 rfl rfl
private theorem pc1w90 : PetersenPackedPin.project cycle1 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x30303030 := PetersenWireProjection.derive 1 stored58 stored63 rfl rfl
private theorem pc1w89 : PetersenPackedPin.project cycle1 (0xccccccccccccccccffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc1w90 stored57 rfl rfl
private theorem pc1w91 : PetersenPackedPin.project cycle1 (0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc1w64 pc1w90 rfl rfl
private theorem pc2w93 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w94 : PetersenPackedPin.project cycle2 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored43 stored47 rfl rfl
private theorem pc2w92 : PetersenPackedPin.project cycle2 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 1 pc2w93 pc2w94 rfl rfl
private theorem pc1w96 : PetersenPackedPin.project cycle1 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored59 stored63 rfl rfl
private theorem pc1w95 : PetersenPackedPin.project cycle1 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc1w64 pc1w96 rfl rfl
private theorem pc26w98 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w99 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w97 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc26w98 pc26w99 rfl rfl
private theorem pc30w101 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w100 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w101 stored13 rfl rfl
private theorem pc30w102 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w103 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w104 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w103 pc30w105 rfl rfl
private theorem pc30w107 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w106 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w107 stored13 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w108 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w109 stored13 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w103 pc30w111 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 3 pc30w107 stored13 rfl rfl
private theorem pc30w114 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w115 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 2 pc30w114 pc30w115 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w116 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 3 pc30w117 stored13 rfl rfl
private theorem pc30w119 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w118 : PetersenPackedPin.project extra30 (0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 3 pc30w119 stored13 rfl rfl
theorem b3_1344 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1344 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1344 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w7 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1345 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1345 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1345 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w18 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1346 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1346 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1346 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w22 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1347 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1347 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,false))] s3_1347 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w31 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w25 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1348 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1348 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1348 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1349 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1349 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1349 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w34 rfl)))))))))) (by decide +kernel)
theorem b3_1350 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1350 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_1350 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w36 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w35 rfl)))))))))) (by decide +kernel)
theorem b3_1351 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1351 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1351 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w47 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w38 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1352 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1352 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1352 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w48 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1353 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1353 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,false),(3,false))] s3_1353 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w57 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w51 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1354 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1354 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1354 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w60 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1355 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1355 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1355 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons pc0w61 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1356 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1356 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_1356 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w62 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1357 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1357 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1357 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w63 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1358 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1358 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1358 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w63 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w64 rfl)))))))))) (by decide +kernel)
theorem b3_1359 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1359 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1359 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0x0,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0,0xcccccccc] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w64 rfl)))))))))) (by decide +kernel)
theorem b3_1360 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1360 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1360 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w47 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1361 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1361 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1361 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfafafafa] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w69 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w68 rfl)))))))))) (by decide +kernel)
theorem b3_1362 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1362 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,false))] s3_1362 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w72 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1363 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1363 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,false))] s3_1363 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xa0a0a0a0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w72 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w35 rfl)))))))))) (by decide +kernel)
theorem b3_1364 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1364 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s3_1364 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w47 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1365 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1365 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(5,true))] s3_1365 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0fffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w81 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1366 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1366 := by
  apply PetersenIndexedNode.close (bank := [s4_902,a4065,a4397,s4_2819]) (PetersenIndexedNode.reasons 256 17 173 0x4202610110a088404a000504021010c444420231111080920009000480821010a4044202210910808a08070603830141011808840442062101094044202210510808908028201410121005040382014180a081080084004202018080c0442024260018080c0426221311018080c0416020309018080c040e0203050180924248404490921010840448082101322214504a080514128200a08090802820242005444282015110a0800c048480030121201242484044909210108404424021011202884806260313010900848050404941109005444282015110a0800c04464003011090006020301018120c09080a0302018110808c2c0030201810848042400302018104c0806240302018102c080614030201810180842480302109000c0806042120109000c0806042120501021010c444420231111080842022101383014100e0c05040141012100504048401311018084c44060280014000600070000313010900c4c04240109000c0842400302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_902 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2638 theta)
    · exact b4_2819 theta
theorem b3_1367 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1367 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1367 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w87 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1368 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1368 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1368 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w89 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1369 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1369 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1369 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w91 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1370 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1370 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(0,true))] s3_1370 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xffffaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w92 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1371 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1371 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1371 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w33 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w95 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1372 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1372 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,false),(1,false))] s3_1372 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w97 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1373 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1373 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1373 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w100 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1374 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1374 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(3,true),(6,true))] s3_1374 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w103 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w102 rfl)))))))))) (by decide +kernel)
theorem b3_1375 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1375 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1375 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w104 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1376 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1376 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1376 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w104 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1377 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1377 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1377 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w106 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1378 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1378 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1378 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1379 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1379 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1379 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1380 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1380 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(6,true))] s3_1380 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w109 rfl)))))))))) (by decide +kernel)
theorem b3_1381 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1381 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1381 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w110 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1382 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1382 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,false),(6,true))] s3_1382 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff0000000000ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w112 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1383 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1383 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(1,false),(6,true))] s3_1383 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f000000000f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w113 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1384 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1384 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true)),(false,(1,false),(6,true))] s3_1384 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf000f000f000f000f000f000f000f00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w116 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1385 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1385 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,true)),(false,(1,false),(6,true))] s3_1385 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf000f000f000f000f000f000f000f0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w59 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w118 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
