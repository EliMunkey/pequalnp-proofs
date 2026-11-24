import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S3
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S12
import Q1020K12L3S13
import Q1020K12L3S14
import Q1020K12L3S15
import Q1020K12L3S16
import Q1020K12L3S19
import Q1020K12L3S20
import Q1020K12L3S21
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S24
import Q1020K12L3S25
import Q1020K12L3S30
import Q1020K12L3S31
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S37
import Q1020K12L3S39
import Q1020K12L3S40
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w8 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored0 stored1 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored0 stored1 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl








private theorem pc30w39 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w41 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl
private theorem pc30w40 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w41 stored8 rfl rfl








private theorem pc34w50 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w52 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl
private theorem pc34w51 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w52 stored16 rfl rfl








private theorem pc3w61 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w63 stored33 rfl rfl








private theorem pc2w72 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w74 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w73 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc2w74 stored41 rfl rfl
private theorem pc3w76 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w75 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w76 stored33 rfl rfl







private theorem pc0w84 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w86 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc0w84 stored49 rfl rfl
private theorem pc30w87 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc34w88 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored16 stored19 rfl rfl
private theorem pc3w89 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl








private theorem pc32w98 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored25 stored28 rfl rfl
private theorem pc32w99 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc34w100 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored17 stored19 rfl rfl








private theorem pc1w109 : PetersenPackedPin.project cycle1 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored58 rfl rfl
private theorem pc1w110 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
theorem b2_42 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_42 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true))] s2_42 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_43 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_43 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true))] s2_43 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x55550000555500005555000055550000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_44 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_44 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true))] s2_44 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x55555555555555550000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_45 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_45 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true))] s2_45 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x50505050505050505050505050505050,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_46 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_46 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true))] s2_46 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_47 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_47 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true))] s2_47 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_48 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_48 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true))] s2_48 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_49 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_49 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true))] s2_49 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_50 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_50 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true))] s2_50 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_51 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_51 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,true))] s2_51 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_52 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_52 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,false))] s2_52 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_53 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_53 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s2_53 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_54 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_54 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,false))] s2_54 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_55 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_55 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false))] s2_55 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_56 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_56 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false))] s2_56 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f00000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_57 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_57 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true))] s2_57 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_58 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_58 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,false))] s2_58 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_59 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_59 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_59 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_60 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_60 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s2_60 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_61 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_61 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true))] s2_61 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w28 rfl)))))))))) (by decide +kernel)
theorem b2_62 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_62 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s2_62 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w29 rfl)))))))))) (by decide +kernel)
theorem b2_63 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_63 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true))] s2_63 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w30 rfl)))))))))) (by decide +kernel)
theorem b2_64 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_64 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_64 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff0000000000ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons pc30w39 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_65 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_65 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s2_65 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b2_66 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_66 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_66 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_67 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_67 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [] s2_67 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_68 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_68 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_68 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w62 (PetersenWireProjection.cons pc3w61 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_69 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_69 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_69 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w73 (PetersenWireProjection.cons pc2w72 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_70 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_70 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_70 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w73 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w74 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_71 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_71 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_71 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w73 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b2_72 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_72 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_72 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w75 (PetersenWireProjection.cons pc3w61 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_73 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_73 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_73 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w86 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w84 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b2_74 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_74 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_74 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w86 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b2_75 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_75 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true))] s2_75 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff0000000000ff00ff00,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w39 (PetersenWireProjection.cons pc30w87 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_76 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_76 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_76 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons pc34w88 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_77 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_77 := by
  apply PetersenIndexedNode.close (bank := [s3_574,s3_561,s3_559,s3_264,s3_234,s3_232,a825,a826,a827,s3_1586,s3_1270,s3_643,s3_382,a828,s3_1333,s3_1336,s3_4,s3_1357,s3_627,s3_529,a829,s3_1377,s3_1382,a830,s3_329,a831,a832,s3_542,s3_290,a833,a834,s3_629,s3_1449,a835,s3_638,a836,a837,s3_631,s3_1443,s3_1395,s3_635,s3_593,s3_76,a838,a839,s3_1419,s3_633,s3_394,a840,s3_836,s3_841,s3_857,s3_856,s3_628,s3_1053,s3_864,s3_639,s3_614,a841,s3_876,s3_879,a842,s3_339,s3_890,s3_893,s3_616,s3_298,s3_903,s3_912,s3_2,s3_923,s3_630,a843,a844,s3_952,s3_958,s3_992,s3_634,s3_623,s3_640,s3_621,s3_641,s3_618,s3_642,s3_626,s3_625,s3_624,s3_636,s3_622,s3_637,s3_620,s3_619]) (PetersenIndexedNode.reasons 256 17 510 0x18888420221012101185048404622230a090888840421011080a00b7005a5000401354100a08042024011d080862225040188888404e0c0210118889c18062222101282008404901028202400108089080480024041210090104202141010808501048401400084045040280014040a08050102101242008405005828201410141007060383040164e0c07060504014100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a0808404a8882420121014100282014102a220504028205040121009080988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c0500560301018094100262213114015c4c4426225040018080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c050055802a20c06005c838141c0a101200248404210120e04840448086160120208404c2c021011202107024808514120e054500a080802928201450500535041282010702a080494120e05250050408028141012505005148411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808027212000c05004f03012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208026c0131404084048022a1010c445004a31111080a0092420231114012cc444420280241080a008f00461080a8202008a210138304010ce0c05040802114100e0c10044383014102008250401410400fc50404840801f1210050410040141012102007a48401311400ec4c440602801d018084c45003c13110180a00720602801ac00d200668381800420e0600710037801b20e06000483811090400c442400302801800c0842410032109000c0a005e03028017400b5242484048008210108405002b210112022005448082101400b084044808801492022004b00248011a82020008a08080144009e004ca0808000a8202003f001e800e941020038504080114008600405040800d941005445001915110a0820030282015114006854442820800b8a0800c050015030121202002884800301400580c0484808009a1202002500110180a0e0600200301018140038060421208006884800605000f0181084820018212080044001e000d000580024000e0017000a8004c000a00030000)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_574 theta
    · exact b3_561 theta
    · exact b3_559 theta
    · exact b3_264 theta
    · exact b3_234 theta
    · exact b3_232 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_129 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_80 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_82 theta)
    · exact b3_1586 theta
    · exact b3_1270 theta
    · exact b3_643 theta
    · exact b3_382 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_352 theta)
    · exact b3_1333 theta
    · exact b3_1336 theta
    · exact b3_4 theta
    · exact b3_1357 theta
    · exact b3_627 theta
    · exact b3_529 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_311 theta)
    · exact b3_1377 theta
    · exact b3_1382 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_410 theta)
    · exact b3_329 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1332 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1337 theta)
    · exact b3_542 theta
    · exact b3_290 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1376 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1375 theta)
    · exact b3_629 theta
    · exact b3_1449 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1383 theta)
    · exact b3_638 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1391 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1390 theta)
    · exact b3_631 theta
    · exact b3_1443 theta
    · exact b3_1395 theta
    · exact b3_635 theta
    · exact b3_593 theta
    · exact b3_76 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1360 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1366 theta)
    · exact b3_1419 theta
    · exact b3_633 theta
    · exact b3_394 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_340 theta)
    · exact b3_836 theta
    · exact b3_841 theta
    · exact b3_857 theta
    · exact b3_856 theta
    · exact b3_628 theta
    · exact b3_1053 theta
    · exact b3_864 theta
    · exact b3_639 theta
    · exact b3_614 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_299 theta)
    · exact b3_876 theta
    · exact b3_879 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_395 theta)
    · exact b3_339 theta
    · exact b3_890 theta
    · exact b3_893 theta
    · exact b3_616 theta
    · exact b3_298 theta
    · exact b3_903 theta
    · exact b3_912 theta
    · exact b3_2 theta
    · exact b3_923 theta
    · exact b3_630 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_562 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_81 theta)
    · exact b3_952 theta
    · exact b3_958 theta
    · exact b3_992 theta
    · exact b3_634 theta
    · exact b3_623 theta
    · exact b3_640 theta
    · exact b3_621 theta
    · exact b3_641 theta
    · exact b3_618 theta
    · exact b3_642 theta
    · exact b3_626 theta
    · exact b3_625 theta
    · exact b3_624 theta
    · exact b3_636 theta
    · exact b3_622 theta
    · exact b3_637 theta
    · exact b3_620 theta
    · exact b3_619 theta
theorem b2_78 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_78 := by
  apply PetersenIndexedNode.close (bank := [s3_600,a845,s3_591,s3_129,s3_77,s3_74,a846,a847,a848,s3_1673,a849,s3_660,s3_383,a850,a851,a852,a853,a854,s3_650,s3_530,a855,a856,a857,a858,s3_330,a859,a860,s3_543,s3_291,a861,a862,a863,a864,a865,s3_659,s3_562,s3_237,a866,a867,a868,a869,a870,a871,a872,s3_655,a873,s3_654,s3_409,a874,s3_835,s3_842,s3_855,s3_854,s3_651,s3_1054,s3_865,a875,a876,a877,s3_875,s3_874,s3_652,s3_1047,s3_880,a878,a879,s3_351,s3_889,s3_894,a880,s3_310,s3_902,s3_913,a843,a881,s3_926,s3_933,s3_2,s3_949,a882,s3_998,a883,a884,a885,s3_648,a886,s3_647,a887,a888,a889,a890,s3_656,s3_649,s3_657,a891,s3_658,s3_646,s3_645]) (PetersenIndexedNode.reasons 256 17 510 0x200c300606202401458504c28242024013d0808a0201080a80010808a0805000280814100a0204202084044203005e1080884058504614130a0c017cc28261416141084044202901028202400108089080480024041210090104202141010809005c48402420185045040282040174a08050406141242012100311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a0810808c88814100a081850448402420322209080484061410a0805040280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c05005a0301018098504c4c062404016d898084c06141018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c050059802c20c06005c838141c0a101200248404614120e058500c888616030a018504c2c061413222107028381150520e0454142101802b084045415005715050840507022101494120e0525005040802a141012505005548411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808029212000c05005303012120107028480428280c080604840441c1210110a0a83824202a10100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b00424021208028c0141888884048026a1012009f004e210130a0a009a420230a0c012cc2822101802508404c283004c30a0884060092210128204011ca0809080802324200a0810048282024202008a908024204010c9080282080210a0809081004424200a08200822820801ec00f200760602801d0180a0081003f801f0180a00720602801ac00d200668381800420e0600710037801b20e060004838130b0400c4c2c00302801800c08c2c1003230b000c0a005e03028017400b524248404800821012005300288013b0a0a0008c2828016400ae0054c2828000b0a08541500251505084060048210115054009854142101801188406003f001e800e941020038504080114008600405040800d941005445001915110a0820030282015114006854442820800b8a0800c050015030121202002884800301400580c0484808009a1202002500110180a0e0600200301018140038060421208006884800605000f0181084820018212080044001e000d000580024000e0017000a8004c000a00030000)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_600 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_591 theta)
    · exact b3_591 theta
    · exact b3_129 theta
    · exact b3_77 theta
    · exact b3_74 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_129 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_74 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_77 theta)
    · exact b3_1673 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_660 theta)
    · exact b3_660 theta
    · exact b3_383 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_351 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_889 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_894 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_949 theta)
    · exact b3_650 theta
    · exact b3_530 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_310 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_902 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_913 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_409 theta)
    · exact b3_330 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_835 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_842 theta)
    · exact b3_543 theta
    · exact b3_291 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_875 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_874 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_652 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1047 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_880 theta)
    · exact b3_659 theta
    · exact b3_562 theta
    · exact b3_237 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_926 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_933 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_855 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_854 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_651 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1054 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_865 theta)
    · exact b3_655 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_998 theta)
    · exact b3_654 theta
    · exact b3_409 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_330 theta)
    · exact b3_835 theta
    · exact b3_842 theta
    · exact b3_855 theta
    · exact b3_854 theta
    · exact b3_651 theta
    · exact b3_1054 theta
    · exact b3_865 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_655 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_543 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_291 theta)
    · exact b3_875 theta
    · exact b3_874 theta
    · exact b3_652 theta
    · exact b3_1047 theta
    · exact b3_880 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_659 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_383 theta)
    · exact b3_351 theta
    · exact b3_889 theta
    · exact b3_894 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_530 theta)
    · exact b3_310 theta
    · exact b3_902 theta
    · exact b3_913 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_562 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_237 theta)
    · exact b3_926 theta
    · exact b3_933 theta
    · exact b3_2 theta
    · exact b3_949 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_650 theta)
    · exact b3_998 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_654 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_649 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_657 theta)
    · exact b3_648 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_656 theta)
    · exact b3_647 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_658 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_646 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_645 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_648 theta)
    · exact b3_656 theta
    · exact b3_649 theta
    · exact b3_657 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_647 theta)
    · exact b3_658 theta
    · exact b3_646 theta
    · exact b3_645 theta
theorem b2_79 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_79 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_79 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w61 (PetersenWireProjection.cons pc3w89 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_80 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_80 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_80 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w99 (PetersenWireProjection.cons pc32w98 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_81 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_81 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_81 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons pc34w100 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_82 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_82 := by
  apply PetersenIndexedNode.close (bank := [s3_68,a892,s3_65,s3_608,s3_607,s3_606,a893,a894,a895,s3_1720,a896,s3_680,s3_384,a897,a898,a899,a900,a901,s3_670,s3_531,a902,a903,a904,a905,s3_331,a906,a907,s3_544,s3_292,a908,a909,a910,a911,a912,s3_678,s3_564,s3_239,a913,a914,a915,a916,a917,s3_674,s3_594,s3_81,a918,a919,a920,s3_673,a921,a922,s3_832,s3_843,a923,a924,s3_848,s3_847,s3_669,s3_1055,s3_866,a925,a926,a927,s3_872,s3_881,a928,a929,s3_885,s3_895,a930,a931,s3_900,s3_899,s3_671,s3_1038,s3_914,a932,s3_2,s3_918,a933,s3_973,a934,a935,a844,s3_960,s3_983,a936,a937,s3_667,a938,s3_664,a939,s3_679,a940,s3_675,a941,a942,s3_668,s3_676,a943,s3_677,s3_666,s3_665]) (PetersenIndexedNode.reasons 256 17 510 0x18888420221012101185048404622230a090888840421011080940406141501021011c18084045010383014040840430a0a101200cd00653080c0144c282614121014013c8404901028202400108089080480024041210090104202141010808501048401400084045040280014040a080501021012420084050063282014100c2827060382040190e0c0506030a094100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a08084050061242012100c28228201410401885040282030a0921009080988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c046545030101808c28226221311195144c44262230a0818080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c050060802fa0c060060838141c0a101200248404210120e04840448086160120208404c2c021011202107024808802da0e0507026141802d1850600bd005d802e1850507026141494120e0525005040802c141012505005948411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c048480802b212000c05005703012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030230a080c080604e0c0109008480c28221201090383000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b0042402120501040151404084048029a10114041005550102101200a484048028c0140c444420280269080a009f004e108098506009a21018024c0122008e50408023141020099004b802514102008a504014104010c5040484080211210050410044141012102008248401311400fc4c440602801f018084c45004013110180a007a0602801cc00e2006e8381801b20e060079003b801d20e06006a83811090400cc42400302801900c0842410034109000c0a006203028018400bd242484048008210108405002d210112022005848082101400b884044808801592022004f0026801298506004861418015400a600506141801198506003f001e800e941020038504080114008600405040800d941005445001915110a0820030282015114006854442820800b8a0800c050015030121202002884800301400580c0484808009a1202002500110180a0e0600200301018140038060421208006884800605000f0181084820018212080044001e000d000580024000e0017000a8004c000a00030000)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_68 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_65 theta)
    · exact b3_65 theta
    · exact b3_608 theta
    · exact b3_607 theta
    · exact b3_606 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_608 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_606 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_607 theta)
    · exact b3_1720 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_680 theta)
    · exact b3_680 theta
    · exact b3_384 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_355 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_832 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_843 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_918 theta)
    · exact b3_670 theta
    · exact b3_531 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_317 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_885 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_895 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_413 theta)
    · exact b3_331 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_872 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_881 theta)
    · exact b3_544 theta
    · exact b3_292 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_900 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_899 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_671 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1038 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_914 theta)
    · exact b3_678 theta
    · exact b3_564 theta
    · exact b3_239 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_848 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_847 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_669 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1055 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_866 theta)
    · exact b3_674 theta
    · exact b3_594 theta
    · exact b3_81 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_960 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_983 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_973 theta)
    · exact b3_673 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_384 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_355 theta)
    · exact b3_832 theta
    · exact b3_843 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_564 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_239 theta)
    · exact b3_848 theta
    · exact b3_847 theta
    · exact b3_669 theta
    · exact b3_1055 theta
    · exact b3_866 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_674 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_413 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_331 theta)
    · exact b3_872 theta
    · exact b3_881 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_531 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_317 theta)
    · exact b3_885 theta
    · exact b3_895 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_544 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_292 theta)
    · exact b3_900 theta
    · exact b3_899 theta
    · exact b3_671 theta
    · exact b3_1038 theta
    · exact b3_914 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_678 theta)
    · exact b3_2 theta
    · exact b3_918 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_670 theta)
    · exact b3_973 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_673 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_594 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_81 theta)
    · exact b3_960 theta
    · exact b3_983 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_668 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_676 theta)
    · exact b3_667 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_677 theta)
    · exact b3_664 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_664 theta)
    · exact b3_679 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_675 theta)
    · exact b3_675 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_666 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_665 theta)
    · exact b3_668 theta
    · exact b3_676 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_667 theta)
    · exact b3_677 theta
    · exact b3_666 theta
    · exact b3_665 theta
theorem b2_83 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_83 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_83 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w110 (PetersenWireProjection.cons pc1w109 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
