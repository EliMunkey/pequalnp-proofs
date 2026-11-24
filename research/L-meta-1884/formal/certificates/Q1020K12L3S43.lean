import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S5
import Q1020K12L4S7
import Q1020K12L4S11
import Q1020K12L4S13
import Q1020K12L4S21
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S61
import Q1020K12L4S67
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc26w7 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w6 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w7 pc26w9 rfl rfl

private theorem pc26w11 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 2 pc26w7 pc26w13 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w15 pc26w9 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffff5050ffff5050ffff5050ffff5050 := PetersenWireProjection.derive 1 pc26w17 pc26w15 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc26w13 pc26w19 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc26w17 pc26w19 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 0 pc26w13 pc26w9 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w23 stored2 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xafafaaaaafafaaaaafafaaaaafafaaaa := PetersenWireProjection.derive 3 pc26w25 stored1 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xafafafafafafafafaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w27 stored1 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w29 stored1 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaafafafafafafafafa := PetersenWireProjection.derive 3 pc26w31 stored1 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w19 stored1 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000 : BitVec 256) = 0xaaaafafaaaaafafaaaaafafaaaaafafa := PetersenWireProjection.derive 3 pc26w7 stored1 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w35 stored1 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0 := PetersenWireProjection.derive 0 pc26w17 pc26w13 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xfafaaaaafafaaaaafafaaaaafafaaaaa := PetersenWireProjection.derive 3 pc26w38 stored1 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w40 stored1 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w9 stored1 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w13 stored0 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w23 stored0 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored4 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 1 stored1 stored4 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 1 pc26w47 pc26w48 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xffffffff00000000ffffffffffff0000 := PetersenWireProjection.derive 3 pc26w29 stored4 rfl rfl
private theorem pc26w50 : PetersenPackedPin.project extra26 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffffffffaaaa0000ffffffffaaaa0000 := PetersenWireProjection.derive 3 pc26w23 stored4 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f00000fffffffff0f00000 := PetersenWireProjection.derive 3 pc26w38 stored4 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored2 stored4 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0ffffffff00000000 := PetersenWireProjection.derive 0 pc26w47 pc26w53 rfl rfl








private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored17 stored23 rfl rfl
private theorem pc34w64 : PetersenPackedPin.project extra34 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored18 stored23 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 1 pc34w62 pc34w64 rfl rfl
private theorem pc34w67 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc34w66 : PetersenPackedPin.project extra34 (0xffff0000000000000000000000000000ffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 pc34w67 stored17 rfl rfl
private theorem pc34w68 : PetersenPackedPin.project extra34 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 2 stored19 stored23 rfl rfl
private theorem pc34w65 : PetersenPackedPin.project extra34 (0xaaaa0000ffff0000aaaa0000aaaa0000aaaa0000ffff0000aaaa0000aaaa : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc34w66 pc34w68 rfl rfl
private theorem pc34w69 : PetersenPackedPin.project extra34 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored16 stored17 rfl rfl
private theorem pc34w71 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w70 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc34w71 stored18 rfl rfl
private theorem pc34w72 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w73 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored16 stored18 rfl rfl
private theorem pc34w74 : PetersenPackedPin.project extra34 (0xcccc0000cccc00000000000000000000cccc0000cccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc34w71 stored17 rfl rfl
private theorem pc34w75 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w77 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc000000000000cccc0000cccc0000cccc00000000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 0 pc34w76 pc34w71 rfl rfl
private theorem pc34w78 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl
private theorem pc34w79 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 pc34w71 stored16 rfl rfl
theorem b3_1806 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1806 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(5,true))] s3_1806 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0fffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1807 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1807 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_1807 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1808 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1808 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_1808 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1809 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1809 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_1809 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5050ffff5050ffff5050ffff5050,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1810 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1810 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(0,true),(5,true))] s3_1810 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffffaaaaffffaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1811 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1811 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(0,true),(5,true))] s3_1811 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000fffff0f0fffff0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1812 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1812 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false)),(false,(0,true),(5,true))] s3_1812 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1813 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1813 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s3_1813 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1814 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1814 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_1814 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1815 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1815 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(1,true))] s3_1815 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafaaaaafafaaaaafafaaaaafafaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1816 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1816 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(1,true))] s3_1816 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xafafafafafafafafaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1817 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1817 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(1,true))] s3_1817 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1818 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1818 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(0,true),(1,true))] s3_1818 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaafafafafafafafafa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w30 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1819 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1819 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_1819 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1820 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1820 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_1820 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1821 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1821 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(1,true))] s3_1821 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1822 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1822 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,false)),(false,(0,true),(5,true))] s3_1822 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1823 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1823 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false)),(false,(0,true),(1,true))] s3_1823 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaaaaafafaaaaafafaaaaafafaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1824 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1824 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(1,true))] s3_1824 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1825 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1825 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,false)),(false,(0,true),(1,true))] s3_1825 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafafafafafafafaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1826 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1826 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(1,true))] s3_1826 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w41 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1827 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1827 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_1827 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w42 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1828 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1828 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true))] s3_1828 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b3_1829 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1829 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true))] s3_1829 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffafafffffafafffffafafffffafa] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w44 rfl)))))))))) (by decide +kernel)
theorem b3_1830 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1830 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true))] s3_1830 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w45 rfl))))))))) (by decide +kernel)
theorem b3_1831 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1831 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_1831 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b3_1832 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1832 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(0,true),(7,true))] s3_1832 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1833 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1833 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true)),(false,(7,true),(5,true))] s3_1833 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w41 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1834 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1834 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s3_1834 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1835 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1835 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(6,true))] s3_1835 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffffffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1836 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1836 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(6,true),(0,true))] s3_1836 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffaaaa0000ffffffffaaaa0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1837 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1837 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false)),(false,(0,true),(6,true))] s3_1837 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffff0f00000fffffffff0f00000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1838 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1838 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(6,true),(0,true))] s3_1838 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffffffff0f0f0f0ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1839 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1839 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_1839 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w65 (PetersenWireProjection.cons pc34w61 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1840 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1840 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(1,false),(3,false))] s3_1840 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w70 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w69 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1841 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1841 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(5,true),(7,true))] s3_1841 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w70 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w72 rfl)))))))))) (by decide +kernel)
theorem b3_1842 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1842 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false)),(false,(7,false),(3,false))] s3_1842 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa0000aaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f00000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w74 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w73 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1843 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1843 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false)),(false,(7,true),(3,true))] s3_1843 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa0000aaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w74 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w75 rfl)))))))))) (by decide +kernel)
theorem b3_1844 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1844 := by
  apply PetersenIndexedNode.close (bank := [s4_1381,a4865,a4866,s4_2579,a4219,a4867,s4_1416,s4_1395,a4868,a4869,a4870,s4_1397,a4871,a4872,a4873,s4_1417,a4874,a4875,s4_1424,a4876,s4_1423,s4_1400,a4877,a4878,a4879,s4_1418,s4_3103,a4880,s4_1422,s4_1408,a4881,a4882,a4883,s4_1414,s4_230,a4884,a4885,s4_1419,a4886,a4887,s4_1421,a4888,a4889,a4890,s4_1425,s4_574,s4_1426]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108090808c282610131111850484444202108088404a0201088a80410808e0c0420228081c1809020420208445080870201088984048404614130809c080c28250202101084448404901028202400108089080480024041210090104202141010808501048401400084045040280014040a080501021012420084042111282008404c2827060108088444e0c0211130a094100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a0808404281824200a0404222282014080a0605040281810889210042229888242012100a0802820141026220504028202820121009080840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c042515030101808422226221088894544c4421151088818080c045444030101808a08016120b09151102c2416122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0492120988a48410809002d42022484a005c9012420204c45080842020988908089011002b24041080a00584202240404c4490102a1a098884c444222262410888a8684c48281a108884c442623002a801484c0600281311098894102000c5040151104c44262228200d8c86c4454441b19098c8a08026221311030104c440c0484800b0a058400c04161403012120026221311428280c080604840441c120c090a0a83824202a101006040302248480c080604420230b0108089212616024049080806040302108880c08060428181090084404222212010888a0600604030228a080c0806045040098904c48a28213120989141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030209888848026201614018100c0826220302018105850424016148012c009200468404801121012005100278013210120042840421014007c84044808800f1202084050020210112022003a4808800cc0062002e2111800b084460039001b800d08446002a2111800a4004d25045040800214102001f000e80068a082001828208009400460020282080058a0800c05000903010584a001016120301400280c04161280038584a000d0005018084c460008030101814000806041312800084c4806050003018104c4a00001312)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1381 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1375 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2340 theta)
    · exact b4_2579 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_7 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2591 theta)
    · exact b4_1416 theta
    · exact b4_1395 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1365 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2330 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2582 theta)
    · exact b4_1397 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1362 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2333 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2332 theta)
    · exact b4_1417 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_3175 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2585 theta)
    · exact b4_1424 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3052 theta)
    · exact b4_1423 theta
    · exact b4_1400 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_298 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2595 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2594 theta)
    · exact b4_1418 theta
    · exact b4_3103 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2839 theta)
    · exact b4_1422 theta
    · exact b4_1408 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_29 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2306 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2833 theta)
    · exact b4_1414 theta
    · exact b4_230 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2328 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2327 theta)
    · exact b4_1419 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3090 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2846 theta)
    · exact b4_1421 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_477 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_478 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_922 theta)
    · exact b4_1425 theta
    · exact b4_574 theta
    · exact b4_1426 theta
theorem b3_1845 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1845 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(0,true),(1,false))] s3_1845 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w77 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w76 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1846 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1846 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false)),(false,(3,false),(5,false))] s3_1846 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w79 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w78 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1847 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1847 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false)),(false,(3,true),(5,true))] s3_1847 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w79 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w76 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
