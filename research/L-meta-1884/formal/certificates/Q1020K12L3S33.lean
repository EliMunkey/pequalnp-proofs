import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S21
import Q1020K12L4S67
import Q1020K12L4S69
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0






private theorem pc30w6 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl

private theorem pc30w5 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 3 pc30w6 stored13 rfl rfl

private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl




private theorem pc2w15 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w14 : PetersenPackedPin.project cycle2 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w15 stored43 rfl rfl




private theorem pc2w21 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl



private theorem pc1w23 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl

private theorem pc1w26 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc1w32 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 stored57 stored59 rfl rfl
private theorem pc1w33 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc2w35 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored41 stored43 rfl rfl
private theorem pc2w36 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored42 stored43 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc2w35 pc2w36 rfl rfl
private theorem pc2w38 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored41 stored47 rfl rfl
private theorem pc2w37 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w38 stored43 rfl rfl
private theorem pc2w40 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl
private theorem pc2w39 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 3 pc2w40 stored43 rfl rfl
private theorem pc2w42 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 2 stored42 stored47 rfl rfl
private theorem pc2w41 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 3 pc2w42 stored43 rfl rfl
private theorem pc1w44 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl
private theorem pc1w45 : PetersenPackedPin.project cycle1 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 stored58 stored59 rfl rfl
private theorem pc1w43 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 pc1w44 pc1w45 rfl rfl
private theorem pc2w47 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w46 : PetersenPackedPin.project cycle2 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc2w15 pc2w47 rfl rfl
private theorem pc2w49 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w48 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w49 stored43 rfl rfl
private theorem pc1w51 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w50 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc1w33 pc1w51 rfl rfl
private theorem pc1w53 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w52 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc1w53 stored59 rfl rfl
private theorem pc2w54 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc1w55 : PetersenPackedPin.project cycle1 (0xffffffffffffffffcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w23 stored57 rfl rfl
private theorem pc2w56 : PetersenPackedPin.project cycle2 (0xffffffffffffffffcccccccccccccccc00000000ffffffff00000000cccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 2 pc2w21 pc2w15 rfl rfl
private theorem pc1w57 : PetersenPackedPin.project cycle1 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc1w33 pc1w23 rfl rfl
private theorem pc2w58 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 pc2w21 pc2w15 rfl rfl



private theorem pc26w61 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl

private theorem pc26w60 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w61 stored1 rfl rfl




private theorem pc26w69 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc30w71 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w70 : PetersenPackedPin.project extra30 (0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 pc30w71 stored9 rfl rfl
private theorem pc2w72 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 pc2w47 stored42 rfl rfl


private theorem pc41w74 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored89 stored95 rfl rfl

private theorem pc41w73 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w74 stored91 rfl rfl





private theorem pc41w83 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored90 rfl rfl
private theorem pc2w84 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffff0000000000000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w36 stored41 rfl rfl
private theorem pc2w86 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w85 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 pc2w86 stored41 rfl rfl
private theorem pc2w88 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w87 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w88 stored41 rfl rfl
private theorem pc41w90 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored89 stored95 rfl rfl
private theorem pc41w89 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w90 stored91 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w61 stored0 rfl rfl
private theorem pc30w92 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 pc30w71 stored8 rfl rfl


private theorem pc32w94 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl

private theorem pc32w93 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc32w94 stored24 rfl rfl





private theorem pc32w103 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl


private theorem pc34w105 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl

private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w105 stored16 rfl rfl





private theorem pc34w114 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc2w116 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 pc2w47 stored41 rfl rfl
private theorem pc41w118 : PetersenPackedPin.project extra41 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored89 stored95 rfl rfl
private theorem pc41w117 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w118 stored91 rfl rfl
theorem b3_1386 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1386 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,false),(3,false))] s3_1386 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf000f000f000f000f000f000f000f000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w5 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1387 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1387 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1387 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w14 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1388 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1388 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1388 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xf0f0f0f0,0xfcfcfcfc,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w26 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w23 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1389 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1389 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1389 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xf0f0f0f0,0x0,0xcccccccc] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w26 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w33 rfl)))))))))) (by decide +kernel)
theorem b3_1390 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1390 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1390 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w34 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1391 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1391 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1391 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w34 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1392 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1392 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1392 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w37 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1393 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1393 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1393 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w37 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1394 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1394 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1394 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfafafafa] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w37 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w38 rfl)))))))))) (by decide +kernel)
theorem b3_1395 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1395 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_1395 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xa0a0a0a,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w39 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1396 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1396 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,true))] s3_1396 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w41 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1397 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1397 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1397 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w43 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1398 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1398 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1398 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w46 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1399 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1399 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_1399 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaa0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w48 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1400 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1400 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1400 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xcccccccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w50 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1401 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1401 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1401 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w52 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1402 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1402 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1402 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w47 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1403 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1403 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1403 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w47 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w54 rfl)))))))))) (by decide +kernel)
theorem b3_1404 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1404 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1404 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w55 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1405 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1405 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1405 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w56 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1406 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1406 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1406 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1407 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1407 := by
  apply PetersenIndexedNode.close (bank := [s4_902,a4065,a4398,s4_2912]) (PetersenIndexedNode.reasons 256 17 170 0x1242484044909210108404c202622210808901042025000282010808a080514128a09410062222101188888404900048002404108089080282014101210052022101108488404504038301c180a0808c044202210310808282015110a88850404a022101108288404484014100a080908028201c100a0c0504084004200210100c048480030101809090006022101313000c0406021311098880c0406020b01018480c0406020701018280c049212420224849080803010180908088480480a212018980c4c042402120141012504424015110a080544428200301119000c044240018120c09080a0302109000c0806042120018110808c2c0030201810848042400302018104c0806240302018102c080614030201810180842480302109000c0806042120501021012000500018001c0000c444420231111080842022101383014100e0c05040141012100504048401311018084c440602313010900c4c04240109000c0842400302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_902 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2829 theta)
    · exact b4_2912 theta
theorem b3_1408 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1408 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1408 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w15 (PetersenWireProjection.cons pc2w54 rfl)))))))))) (by decide +kernel)
theorem b3_1409 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1409 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1409 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w58 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1410 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1410 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,true),(1,true))] s3_1410 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w60 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1411 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1411 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(3,true))] s3_1411 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w70 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1412 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1412 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1412 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w72 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1413 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1413 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1413 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_1414 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1414 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1414 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w83 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w73 rfl)))))))))) (by decide +kernel)
theorem b3_1415 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1415 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1415 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w84 rfl)))))))))) (by decide +kernel)
theorem b3_1416 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1416 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1416 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfafafafa] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w85 rfl)))))))))) (by decide +kernel)
theorem b3_1417 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1417 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1417 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w87 rfl)))))))))) (by decide +kernel)
theorem b3_1418 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1418 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1418 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w83 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w89 rfl)))))))))) (by decide +kernel)
theorem b3_1419 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1419 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1419 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0,0xcccccccc] (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w33 rfl)))))))))) (by decide +kernel)
theorem b3_1420 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1420 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,true),(3,true))] s3_1420 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w91 rfl)))))))))) (by decide +kernel)
theorem b3_1421 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1421 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,true),(6,true))] s3_1421 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w92 rfl)))))))))) (by decide +kernel)
theorem b3_1422 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1422 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(1,true),(3,true))] s3_1422 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc32w103 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w93 rfl)))))))))) (by decide +kernel)
theorem b3_1423 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1423 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_1423 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w114 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w104 rfl)))))))))) (by decide +kernel)
theorem b3_1424 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1424 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(3,true))] s3_1424 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w115 rfl)))))))))) (by decide +kernel)
theorem b3_1425 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1425 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s3_1425 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfafafafa] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w116 rfl)))))))))) (by decide +kernel)
theorem b3_1426 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1426 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1426 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w83 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w117 rfl)))))))))) (by decide +kernel)
theorem b3_1427 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1427 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1427 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w21 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w84 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
