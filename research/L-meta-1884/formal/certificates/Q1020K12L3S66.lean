import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc3w8 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w7 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w8 pc3w9 rfl rfl
private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w13 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w8 pc3w13 rfl rfl







private theorem pc2w21 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w23 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w20 : PetersenPackedPin.project cycle2 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w21 pc2w23 rfl rfl
private theorem pc2w24 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl

private theorem pc3w27 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w27 pc3w28 rfl rfl
private theorem pc2w30 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w29 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w30 pc2w23 rfl rfl
private theorem pc3w32 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w33 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w31 : PetersenPackedPin.project cycle3 (0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 pc3w32 pc3w33 rfl rfl
private theorem pc2w35 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w36 : PetersenPackedPin.project cycle2 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored43 stored47 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 1 pc2w35 pc2w36 rfl rfl
private theorem pc2w38 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored41 stored47 rfl rfl
private theorem pc2w37 : PetersenPackedPin.project cycle2 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 1 pc2w38 pc2w36 rfl rfl
private theorem pc2w39 : PetersenPackedPin.project cycle2 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc2w35 pc2w23 rfl rfl
private theorem pc2w41 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w40 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w41 stored43 rfl rfl
private theorem pc2w42 : PetersenPackedPin.project cycle2 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 stored41 stored42 rfl rfl


private theorem pc0w43 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc0w46 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored49 stored50 rfl rfl





private theorem pc0w52 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl

private theorem pc3w55 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w54 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w55 stored34 rfl rfl
private theorem pc2w57 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w56 : PetersenPackedPin.project cycle2 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w57 stored42 rfl rfl
private theorem pc2w59 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w58 : PetersenPackedPin.project cycle2 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 pc2w59 stored42 rfl rfl
private theorem pc2w61 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored41 stored43 rfl rfl
private theorem pc2w60 : PetersenPackedPin.project cycle2 (0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc2w61 stored42 rfl rfl
private theorem pc2w62 : PetersenPackedPin.project cycle2 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w36 stored42 rfl rfl
private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w27 stored34 rfl rfl


private theorem pc26w66 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl

private theorem pc26w68 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w65 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc26w66 pc26w68 rfl rfl





private theorem pc26w75 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc2w76 : PetersenPackedPin.project cycle2 (0xffffffffffffffffcccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 3 pc2w42 pc2w24 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w75 stored1 rfl rfl
private theorem pc3w78 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 pc3w32 pc3w28 rfl rfl
private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w8 stored34 rfl rfl


private theorem pc30w82 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl

private theorem pc30w84 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f000000000 := PetersenWireProjection.derive 0 pc30w82 pc30w84 rfl rfl




private theorem pc30w90 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl



private theorem pc34w94 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl

private theorem pc34w96 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc34w93 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc34w94 pc34w96 rfl rfl




private theorem pc34w102 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc2w105 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored41 stored43 rfl rfl
private theorem pc2w104 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w105 stored42 rfl rfl
private theorem pc2w106 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
private theorem pc2w107 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 pc2w23 stored42 rfl rfl


private theorem pc74w108 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl





private theorem pc74w116 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl

private theorem pc26w118 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w68 stored0 rfl rfl
private theorem pc2w120 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc2w119 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccc00000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc2w120 pc2w24 rfl rfl
private theorem pc3w121 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w28 stored33 rfl rfl
private theorem pc30w122 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w84 stored8 rfl rfl
private theorem pc34w123 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w96 stored16 rfl rfl
private theorem pc2w124 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w24 stored41 rfl rfl
private theorem pc3w125 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w13 stored33 rfl rfl
private theorem pc3w126 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl


private theorem pc32w127 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl

private theorem pc32w130 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl




private theorem pc32w136 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl

private theorem pc34w138 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
theorem b3_2772 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2772 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2772 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w7 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2773 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2773 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2773 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w12 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2774 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2774 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2774 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w20 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2775 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2775 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s3_2775 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2776 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2776 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2776 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w29 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2777 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2777 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true))] s3_2777 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w31 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2778 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2778 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(0,true))] s3_2778 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xffffaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w34 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2779 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2779 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,true),(0,true))] s3_2779 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xfafafafa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w37 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2780 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2780 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2780 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w39 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2781 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2781 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s3_2781 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaa0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w40 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2782 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2782 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2782 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w23 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2783 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2783 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,false),(4,false))] s3_2783 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f00000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w42 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2784 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2784 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(1,false))] s3_2784 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w52 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w46 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w43 rfl)))))))))) (by decide +kernel)
theorem b3_2785 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2785 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2785 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w54 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2786 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2786 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2786 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w56 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2787 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2787 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_2787 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w58 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2788 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2788 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,true),(4,true))] s3_2788 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xfffff0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w60 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2789 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2789 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2789 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w62 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2790 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2790 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true))] s3_2790 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xfffff0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2791 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2791 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(1,false),(3,false))] s3_2791 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w75 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w65 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2792 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2792 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,false),(2,false))] s3_2792 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f00000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w76 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2793 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2793 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(1,true))] s3_2793 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w75 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2794 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2794 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,false))] s3_2794 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f00000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w78 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2795 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2795 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2795 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w79 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2796 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2796 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(0,true))] s3_2796 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w35 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2797 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2797 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(2,false)),(false,(1,false),(4,false))] s3_2797 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f000000000f0f0f0f000000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w90 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_2798 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2798 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(1,false),(3,false))] s3_2798 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff00000000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w93 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2799 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2799 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2799 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w104 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2800 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2800 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2800 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w106 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2801 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2801 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_2801 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w107 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2802 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2802 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2802 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2803 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2803 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2803 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w116 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w108 rfl)))))))))) (by decide +kernel)
theorem b3_2804 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2804 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(1,true),(3,true))] s3_2804 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w75 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w118 rfl)))))))))) (by decide +kernel)
theorem b3_2805 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2805 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_2805 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w119 rfl)))))))))) (by decide +kernel)
theorem b3_2806 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2806 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_2806 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w121 rfl)))))))))) (by decide +kernel)
theorem b3_2807 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2807 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(3,true),(6,true))] s3_2807 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w90 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w122 rfl)))))))))) (by decide +kernel)
theorem b3_2808 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2808 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(5,true),(7,true))] s3_2808 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w123 rfl)))))))))) (by decide +kernel)
theorem b3_2809 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2809 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,true),(4,true))] s3_2809 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w124 (PetersenWireProjection.cons pc2w120 rfl)))))))))) (by decide +kernel)
theorem b3_2810 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2810 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2810 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w125 rfl))))))))) (by decide +kernel)
theorem b3_2811 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2811 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_2811 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w32 (PetersenWireProjection.cons pc3w126 rfl)))))))))) (by decide +kernel)
theorem b3_2812 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2812 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,false)),(false,(3,true),(5,true))] s3_2812 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w136 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w130 (PetersenWireProjection.cons pc32w127 rfl)))))))))) (by decide +kernel)
theorem b3_2813 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2813 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(0,false)),(false,(7,true),(5,true))] s3_2813 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w94 (PetersenWireProjection.cons pc34w138 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
