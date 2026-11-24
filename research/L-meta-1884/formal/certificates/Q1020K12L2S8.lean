import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S10
import Q1020K12L3S17
import Q1020K12L3S18
import Q1020K12L3S19
import Q1020K12L3S28
import Q1020K12L3S31
import Q1020K12L3S35
import Q1020K12L3S42
import Q1020K12L3S44
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S52
import Q1020K12L3S53
import Q1020K12L3S54
import Q1020K12L3S55
import Q1020K12L3S60
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc30w1 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl





private theorem pc30w9 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored11 stored13 rfl rfl
private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w11 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w12 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl




private theorem pc34w16 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl




private theorem pc34w23 : PetersenPackedPin.project extra34 (0xffff0000cccc0000ffff0000cccc0000ffff0000cccc0000ffff0000cccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 1 pc34w16 stored19 rfl rfl
private theorem pc34w24 : PetersenPackedPin.project extra34 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored16 stored17 rfl rfl
private theorem pc34w26 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w25 : PetersenPackedPin.project extra34 (0xffff0000ffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc34w26 stored16 rfl rfl
private theorem pc34w27 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w28 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w29 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w30 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl
private theorem pc34w31 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored16 stored18 rfl rfl
private theorem pc34w32 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w33 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w34 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w35 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w36 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w37 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w32 stored19 rfl rfl
private theorem pc34w39 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w26 pc34w39 rfl rfl
private theorem pc34w41 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w41 pc34w26 rfl rfl







private theorem pc26w49 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl

private theorem pc26w52 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0x8888888800000000888888880000000088888888000000008888888800000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w52 stored2 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w54 : PetersenPackedPin.project extra26 (0x8888888888888888000000000000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w52 stored1 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w56 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888800000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w52 stored0 rfl rfl
private theorem pc26w57 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc26w59 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
theorem b2_336 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_336 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true))] s2_336 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w1 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_337 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_337 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(0,true))] s2_337 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_338 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_338 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true))] s2_338 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w11 rfl)))))))))) (by decide +kernel)
theorem b2_339 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_339 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true))] s2_339 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w12 rfl)))))))))) (by decide +kernel)
theorem b2_340 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_340 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true))] s2_340 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w13 rfl)))))))))) (by decide +kernel)
theorem b2_341 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_341 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s2_341 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafafafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w23 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w16 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_342 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_342 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s2_342 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafafafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w23 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_343 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_343 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false))] s2_343 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff00000000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w25 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w24 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_344 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_344 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false))] s2_344 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff00000000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w25 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_345 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_345 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_345 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w27 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_346 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_346 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s2_346 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w28 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_347 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_347 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false))] s2_347 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w29 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_348 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_348 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,false))] s2_348 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w30 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_349 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_349 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,false))] s2_349 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f00000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w31 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_350 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_350 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s2_350 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w16 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_351 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_351 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false))] s2_351 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w24 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_352 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_352 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s2_352 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w32 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_353 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_353 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true))] s2_353 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_354 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_354 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(0,true))] s2_354 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w34 rfl)))))))))) (by decide +kernel)
theorem b2_355 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_355 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true))] s2_355 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w35 rfl)))))))))) (by decide +kernel)
theorem b2_356 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_356 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_356 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w36 rfl)))))))))) (by decide +kernel)
theorem b2_357 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_357 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_357 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w36 rfl))))))))) (by decide +kernel)
theorem b2_358 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_358 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s2_358 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaaffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w37 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w32 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_359 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_359 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s2_359 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaaffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w37 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_360 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_360 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true))] s2_360 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffff0f0fffff0f0fffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_361 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_361 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true))] s2_361 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffff0f0fffff0f0fffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_362 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_362 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_362 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_363 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_363 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_363 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w36 rfl)))))))))) (by decide +kernel)
theorem b2_364 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_364 := by
  apply PetersenIndexedNode.close (bank := [s3_1802,a1599,s3_2228,s3_2234,s3_1850,a1600,s3_2240,s3_2252,s3_1975,a1601,s3_2258,s3_2266,a1602,a1603,a1604,a1605,a1606,a1607,a1608,a1609,s3_2073,a1610,s3_2276,s3_2292,a1611,s3_314,a1612,a1613,s3_2224,a1614,a1615,s3_2254,s3_2226,a1616,a1617,s3_2268,a1618,a1619,a1620,a1621,a1622,a1623,a1624,a1625,s3_2230,a1626,a1627,s3_2294,a1628,s3_444,a1629,a1630,s3_2236,a1631,a1632,s3_2270,s3_2238,a1633,a1634,s3_2272,s3_2243,a1635,a1636,s3_2287,s3_2245,a1637,a1638,s3_2296,s3_2247,s3_747,a1639,a1640,s3_2256,a1641,a1642,s3_2274,a1643,a1644,a1645,a1646,s3_2260,a1647,a1648,s3_2298,s3_2262,s3_1181,a1649,a1650,a1651,a1652,a1653,a1654,a1655,a1656,a1657,s3_2300,a1658,a1659,a1660,a1661,a1662,a1663,a1664,s3_2302,a1665,s3_1306,a1666,a1667,s3_2289,a1668,a1669,s3_2305]) (PetersenIndexedNode.reasons 256 17 448 0x803731110a00050008036a4001850490008037b111185048444803624000a000500080352c0804202b0008034a4001410090008035ac081410090208034240004202900080331c08042027000803294000c282500080339c080c282502080321400042025000803126020504098008030a4001918090008031a60219180900880302400050409000802f1602050405800802e9400090805000802f9602090805008802e1400050405000802d0a02090802800802c8840450402800802d8a02050402808802c0840490802101802b250100c049400802aa400109009000802ba501109009004802a240000c0490008029150100c04540080289400189805000802995011898050048028140000c0450008027094140c0425018026884044c4421018027894144c4421058026084040c04210180250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c040602802324808060292008022a4001070290008023a4809070290028022240000602900080211480806025200802094000848050008021948088480500280201400006025000801f0a82806020301801e884044c482101801f8a8284c48280a801e0840406020301801d0a88806020301801c8a08016120b01801d8a88816120309801c0a08006020301801b0180806020600801aa12000c080600801b818080c080602801a2120006020301801924404060491008018a4001070490008019a4405070490018018240000604900080171440406045100801694000c2c05000801794404c2c05001801614000060450008015084040604210080148a020424021008015884044240210180140a020060403028013125040604030280128a08016140b028013925041614030a80120a08006040302801121604060403028010818084a4806028011a16044a48212480100180806040302800f00c0442400300800e8181006040300800f80c0406040301800e0181042400604800d31110a0808404800ca400121009000800db11112100d040800c24000a0809000800b30a0921004202800a94000a0805000800bb0a08a0805040800a1400121005000800918504a0805040800888404e0c02101800998504e0c07040800808404a0802101800712100a080484080068a081311028208007921013110484080060a080a0802820800521200a0805040800481808a88806028005a1200a8885440800401808a0800602800310900a0804240800280c052504030180039090125044240800200c04a0800301800118580a0805040800080c08a2820302800198580a2825140800000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1802 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1800 theta)
    · exact b3_2228 theta
    · exact b3_2234 theta
    · exact b3_1850 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_366 theta)
    · exact b3_2240 theta
    · exact b3_2252 theta
    · exact b3_1975 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1798 theta)
    · exact b3_2258 theta
    · exact b3_2266 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1975 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1798 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2258 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2266 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1850 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_366 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2240 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2252 theta)
    · exact b3_2073 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_314 theta)
    · exact b3_2276 theta
    · exact b3_2292 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2073 theta)
    · exact b3_314 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2276 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2292 theta)
    · exact b3_2224 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1184 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2081 theta)
    · exact b3_2254 theta
    · exact b3_2226 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1978 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1980 theta)
    · exact b3_2268 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2226 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1978 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1980 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2268 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2224 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1184 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2081 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2254 theta)
    · exact b3_2230 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_444 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1859 theta)
    · exact b3_2294 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2230 theta)
    · exact b3_444 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1859 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2294 theta)
    · exact b3_2236 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2078 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1190 theta)
    · exact b3_2270 theta
    · exact b3_2238 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1854 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_447 theta)
    · exact b3_2272 theta
    · exact b3_2243 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_760 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_760 theta)
    · exact b3_2287 theta
    · exact b3_2245 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1306 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1312 theta)
    · exact b3_2296 theta
    · exact b3_2247 theta
    · exact b3_747 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_813 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2302 theta)
    · exact b3_2256 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1805 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1805 theta)
    · exact b3_2274 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2238 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_447 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1854 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2272 theta)
    · exact b3_2260 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_448 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1855 theta)
    · exact b3_2298 theta
    · exact b3_2262 theta
    · exact b3_1181 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2077 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2300 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2236 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1190 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2078 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2270 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2262 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1181 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2077 theta)
    · exact b3_2300 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2260 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_448 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1855 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2298 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2247 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_747 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_813 theta)
    · exact b3_2302 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2245 theta)
    · exact b3_1306 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1312 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2296 theta)
    · exact b3_2289 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_783 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_783 theta)
    · exact b3_2305 theta
theorem b2_365 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_365 := by
  apply PetersenIndexedNode.close (bank := [s3_1803,a1670,s3_2229,s3_2235,s3_1851,a1671,s3_2241,s3_2253,s3_1976,a1672,s3_2259,s3_2267,a1673,a1674,a1675,a1676,a1677,a1678,a1679,a1680,s3_2075,s3_2074,a1681,a1682,s3_2277,s3_2293,a1683,a1684,s3_316,s3_315,a1685,a1686,s3_7,s3_8,a1687,a1688,s3_2278,s3_2279,s3_2225,a1689,a1690,s3_2255,s3_2227,a1691,a1692,s3_2269,a1693,a1694,a1695,a1696,a1697,a1698,a1699,a1700,s3_2231,a1701,a1702,s3_2295,a1703,s3_445,a1704,a1705,s3_2232,s3_2233,s3_51,s3_52,a1706,a1707,s3_2309,s3_2306,s3_2237,a1708,a1709,s3_2271,s3_2239,a1710,a1711,s3_2273,s3_2244,a1712,a1713,s3_2288,s3_2246,a1714,a1715,s3_2297,s3_2248,s3_748,a1716,a1717,s3_2312,a1718,s3_2250,s3_2251,s3_95,s3_96,a1719,a1720,s3_2310,s3_2307,s3_2257,a1721,a1722,s3_2275,a1723,a1724,a1725,a1726,s3_2261,a1727,a1728,a1729,a1730,s3_2299,s3_2263,s3_1182,a1731,a1732,s3_2264,s3_2265,s3_162,s3_163,a1733,a1734,s3_2311,s3_2308,a1735,a1736,a1737,a1738,a1739,a1740,a1741,s3_2301,a1742,a1743,a1744,a1745,s3_2313,a1746,a1747,a1748,a1749,a1750,a1751,a1752,a1753,a1754,a1755,a1756,a1757,a1758,a1759,s3_2303,a1760,s3_1307,a1761,a1762,a1763,a1764,a1765,a1766,a1767,a1768,a1769,a1770,a1771,s3_2291,s3_2290,a1772,a1773,a1774,a1775,a1669,a1668]) (PetersenIndexedNode.reasons 256 17 548 0x8055402ba015290008010c0081888890008056402b6015650008010c0081850450008056311120156c4448055402a58504c28280544029e014c84448051c0288420221018050c0280c28261418052c0290c2826141804fc027842022101804e3818042022101804db11114100e040804eb81814100e060804d3111042022101804bc025842022101804ab0a08c2826141804cc0260c2826141804a30a08420221018048c0240504028208047c0238908048408049c0248908048408046c0230504028208044c0220504028208043b11119180c8408045c0229918048c080433111050402820804232220504028208041b0a08908048408042b222090804840804130a085040282080400a02090802800803f884045040280080408a02050402808803f0840490802101803dc01e80c040602803cc01e109008480803ec01f109008480803bc01d80c040602803a311100c0406028039b81810900c440803ab11110900c4448039381800c0406028037c01b80c0406028036b0a098980c4808038c01c1898084c0803630a080c0406028035094140c0425018034884044c4421018035894144c4421058034084040c04210180330b0900c04060280328a0801c140e0280338b0901c14060a80320a0800c0406028030c018006020301802fc0178848042408031c018884804240802ec017006020301802cc016006020301802bb11110702c240802dc016907028381802b3111006020301802a30a08060203018029b222084804240802ab0a08848042408029322200602030180280a828060203018027884044c48210180288a8284c48280a8027084040602030180260a8880602030180258a08016120b0180268a8881612030980250a08006020301802401808060206008023a12000c0806008024818080c080602802321200060203018021c0108060403028020c0100c2c061608022c0110c2c06160801fc00f806040302801e3151406040302801db11110704c444801eb15150704c445801d3111006040302801c3262406040302801bb0a08c2c06160801cb2624c2c06160801b30a0806040302801a084040604210080198a02042402100801a884044240210180190a020060403028018125040604030280178a08016140b028018925041614030a80170a08006040302801621604060403028015818084a4806028016a16044a48212480150180806040302801400c044240030080138181006040300801480c0406040301801301810424006048012c0092004700228010c0080a0805040800f31110a0805040800ec007121009080800fb11112100d040800dc0068a0805040800c30a0921009080800bc0058a0805040800cb0a08a0805040800ac005121009080800918504a0805040800888404e0c02101800998504e0c07040800808404a0802101800712100a080484080068a081311028208007921013110484080060a080a0802820800521200a0805040800481808a88806028005a1200a8885440800401808a0800602800310900a0804240800280c052504030180039090125044240800200c04a0800301800118580a0805040800080c08a2820302800198580a2825140800000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1803 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1799 theta)
    · exact b3_2229 theta
    · exact b3_2235 theta
    · exact b3_1851 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_365 theta)
    · exact b3_2241 theta
    · exact b3_2253 theta
    · exact b3_1976 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1797 theta)
    · exact b3_2259 theta
    · exact b3_2267 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1976 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1797 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2259 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2267 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1851 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_365 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2241 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2253 theta)
    · exact b3_2075 theta
    · exact b3_2074 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_316 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_315 theta)
    · exact b3_2277 theta
    · exact b3_2293 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2075 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2074 theta)
    · exact b3_316 theta
    · exact b3_315 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2277 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2293 theta)
    · exact b3_7 theta
    · exact b3_8 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2534 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2528 theta)
    · exact b3_2278 theta
    · exact b3_2279 theta
    · exact b3_2225 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1183 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2080 theta)
    · exact b3_2255 theta
    · exact b3_2227 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1977 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1979 theta)
    · exact b3_2269 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2227 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1977 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1979 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2269 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2225 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1183 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2080 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2255 theta)
    · exact b3_2231 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_445 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1858 theta)
    · exact b3_2295 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2231 theta)
    · exact b3_445 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1858 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2295 theta)
    · exact b3_2232 theta
    · exact b3_2233 theta
    · exact b3_51 theta
    · exact b3_52 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2057 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2056 theta)
    · exact b3_2309 theta
    · exact b3_2306 theta
    · exact b3_2237 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2079 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1189 theta)
    · exact b3_2271 theta
    · exact b3_2239 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1853 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_446 theta)
    · exact b3_2273 theta
    · exact b3_2244 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_759 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_759 theta)
    · exact b3_2288 theta
    · exact b3_2246 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1307 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1311 theta)
    · exact b3_2297 theta
    · exact b3_2248 theta
    · exact b3_748 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_814 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_812 theta)
    · exact b3_2312 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2303 theta)
    · exact b3_2250 theta
    · exact b3_2251 theta
    · exact b3_95 theta
    · exact b3_96 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1504 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1503 theta)
    · exact b3_2310 theta
    · exact b3_2307 theta
    · exact b3_2257 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1804 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1804 theta)
    · exact b3_2275 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2239 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_446 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1853 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2273 theta)
    · exact b3_2261 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_449 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1857 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1856 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2313 theta)
    · exact b3_2299 theta
    · exact b3_2263 theta
    · exact b3_1182 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2076 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2301 theta)
    · exact b3_2264 theta
    · exact b3_2265 theta
    · exact b3_162 theta
    · exact b3_163 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2203 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2202 theta)
    · exact b3_2311 theta
    · exact b3_2308 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2237 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1189 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2079 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2271 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2263 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1182 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2076 theta)
    · exact b3_2301 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2261 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_449 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1857 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1856 theta)
    · exact b3_2313 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2299 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2264 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2265 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_162 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_163 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2203 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2202 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2311 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2308 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2248 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_748 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_814 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_812 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2312 theta)
    · exact b3_2303 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2246 theta)
    · exact b3_1307 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1311 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2297 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2250 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2251 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_95 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_96 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1504 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1503 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2310 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2307 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2291 theta)
    · exact b3_2291 theta
    · exact b3_2290 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_785 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_784 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_785 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_784 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_783 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_783 theta)
theorem b2_366 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_366 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_366 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_367 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_367 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_367 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_368 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_368 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s2_368 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_369 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_369 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_369 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_370 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_370 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false))] s2_370 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w56 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_371 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_371 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_371 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w56 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_372 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_372 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_372 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_373 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_373 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s2_373 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_374 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_374 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false))] s2_374 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_375 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_375 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false))] s2_375 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w57 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_376 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_376 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false))] s2_376 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f00000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w58 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_377 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_377 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s2_377 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
