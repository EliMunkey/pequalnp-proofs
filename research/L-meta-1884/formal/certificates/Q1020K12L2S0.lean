import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S60
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S71
import Q1020K12L3S72
import Q1020K12L3S73
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
import Q1020K12L3S81
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w8 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl

private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w16 stored0 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl








private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w27 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w28 stored33 rfl rfl








private theorem pc30w38 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w37 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w38 stored8 rfl rfl
private theorem pc30w39 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl








private theorem pc34w49 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored17 stored19 rfl rfl
private theorem pc34w48 : PetersenPackedPin.project extra34 (0xffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w49 stored16 rfl rfl
private theorem pc34w50 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w52 stored0 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc3w55 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w54 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w55 stored33 rfl rfl
private theorem pc34w56 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w58 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w58 stored16 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc34w61 stored16 rfl rfl
private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored16 stored17 rfl rfl
private theorem pc34w64 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w63 : PetersenPackedPin.project extra34 (0xffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 pc34w64 stored16 rfl rfl








private theorem pc32w73 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w75 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored28 stored29 rfl rfl
private theorem pc32w74 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w75 stored24 rfl rfl
private theorem pc32w76 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl
private theorem pc32w78 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored26 stored28 rfl rfl
private theorem pc32w77 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 1 pc32w78 stored24 rfl rfl
private theorem pc32w79 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored24 stored25 rfl rfl
private theorem pc32w81 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored28 rfl rfl
private theorem pc32w80 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 1 pc32w81 stored24 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0x88888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w83 stored0 rfl rfl
private theorem pc26w85 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w85 stored0 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w88 stored0 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
theorem b2_0 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_0 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_0 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_1 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_1 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s2_1 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_2 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_2 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_2 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_3 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_3 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s2_3 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_4 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_4 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s2_4 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_5 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_5 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_5 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_6 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_6 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_6 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_7 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_7 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_7 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_8 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_8 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s2_8 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w17 rfl)))))))))) (by decide +kernel)
theorem b2_9 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_9 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_9 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w27 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_10 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_10 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_10 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w27 (PetersenWireProjection.cons pc3w28 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_11 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_11 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_11 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w27 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b2_12 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_12 := by
  apply PetersenIndexedNode.close (bank := [s3_44,s3_43,a763,s3_2710,a764,a765,s3_112,s3_62,a766,a767,a768,s3_63,s3_41,a769,a770,s3_64,s3_40,a771,a772,s3_118,s3_3409,a773,s3_153,s3_69,a774,a775,a776,a777,a778,s3_149,s3_3360,a779,s3_142,s3_21,s3_0,a780,a781,s3_136,s3_108,s3_45,s3_107,s3_135,s3_91,s3_154,s3_103,s3_145,s3_111,s3_110,s3_105,s3_106,s3_104,s3_99,s3_150,s3_113,s3_70,s3_100,s3_137,s3_97,s3_146,s3_114,s3_71,s3_98,s3_138,s3_92,s3_151,s3_93,s3_147,s3_116,s3_117,s3_115,s3_72,s3_95,s3_96,s3_94,s3_139,s3_88,s3_152,s3_121,s3_73,s3_90,s3_140,s3_124,s3_123,s3_78,s3_83,s3_82,s3_77]) (PetersenIndexedNode.reasons 256 17 498 0x200ad005342024008988888404802ac0150901100226141120218889005462224014d8504c2828029401450889004f108088406009c614130a0c0140c28261418026884044202e0601080884058888a0807020381814100e0606222084044203004b1080884058504614130a0c0130c28261416141084044203004980244011e008c5040282040128a08050408022c0112008700412820141018888908068204010921009080622214100a081003f48402420185045040282040100a08050406141242012100311128200c4044202706010808c444e0c021111080941004203003d14100a082007848402420400f890804840801d8a0805041003914100a0818888c8c06420400e9918048c062220a0805040c88814100a081850448402420322209080484061410a0805040280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805041003703010180a006c84804240400e109008480801a818080c04c444030101809c0c084806220311110900c4447030018080c0500330301018098504c4c06240400d1898084c06141018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0500328018c00c2004a42402120400be000d002e8016109008480c44441c0b0902005a838141c0b111084804240614120e058500c8882120109018504424021203222107028381150510900541421013130084045414626015050840484802101494110900848050408015141012505002b484114100848042401511109005444282045c48a08054448b8915110a080848028200301109000c0484802322119000c04464403012120084804240801400c080605002730b0185820052616030b0400980604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c0886820302018110900424021208012c0092004700228002400860041001f800f311120008c444800ec00720036c282800230a08541500191505084060030210115054006854142101800b884060027001280089410200205040800b40056002850408007941005445000d15110a082001828201511400385444282080058a0800c050009030121202001084800301400280c0484808003a1202000d000501809090200080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_44 theta
    · exact b3_43 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2704 theta)
    · exact b3_2710 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_18 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2936 theta)
    · exact b3_112 theta
    · exact b3_62 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_42 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2681 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2713 theta)
    · exact b3_63 theta
    · exact b3_41 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2680 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2714 theta)
    · exact b3_64 theta
    · exact b3_40 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2538 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2537 theta)
    · exact b3_118 theta
    · exact b3_3409 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2735 theta)
    · exact b3_153 theta
    · exact b3_69 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_31 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2964 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2992 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3363 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3059 theta)
    · exact b3_149 theta
    · exact b3_3360 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_3022 theta)
    · exact b3_142 theta
    · exact b3_21 theta
    · exact b3_0 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3351 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3281 theta)
    · exact b3_136 theta
    · exact b3_108 theta
    · exact b3_45 theta
    · exact b3_107 theta
    · exact b3_135 theta
    · exact b3_91 theta
    · exact b3_154 theta
    · exact b3_103 theta
    · exact b3_145 theta
    · exact b3_111 theta
    · exact b3_110 theta
    · exact b3_105 theta
    · exact b3_106 theta
    · exact b3_104 theta
    · exact b3_99 theta
    · exact b3_150 theta
    · exact b3_113 theta
    · exact b3_70 theta
    · exact b3_100 theta
    · exact b3_137 theta
    · exact b3_97 theta
    · exact b3_146 theta
    · exact b3_114 theta
    · exact b3_71 theta
    · exact b3_98 theta
    · exact b3_138 theta
    · exact b3_92 theta
    · exact b3_151 theta
    · exact b3_93 theta
    · exact b3_147 theta
    · exact b3_116 theta
    · exact b3_117 theta
    · exact b3_115 theta
    · exact b3_72 theta
    · exact b3_95 theta
    · exact b3_96 theta
    · exact b3_94 theta
    · exact b3_139 theta
    · exact b3_88 theta
    · exact b3_152 theta
    · exact b3_121 theta
    · exact b3_73 theta
    · exact b3_90 theta
    · exact b3_140 theta
    · exact b3_124 theta
    · exact b3_123 theta
    · exact b3_78 theta
    · exact b3_83 theta
    · exact b3_82 theta
    · exact b3_77 theta
theorem b2_13 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_13 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s2_13 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b2_14 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_14 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true))] s2_14 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w39 rfl)))))))))) (by decide +kernel)
theorem b2_15 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_15 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [] s2_15 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w48 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_16 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_16 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_16 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w48 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w50 rfl)))))))))) (by decide +kernel)
theorem b2_17 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_17 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_17 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_18 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_18 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s2_18 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w53 rfl)))))))))) (by decide +kernel)
theorem b2_19 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_19 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_19 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w54 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_20 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_20 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_20 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w54 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b2_21 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_21 := by
  apply PetersenIndexedNode.close (bank := [s3_201,a782,a783,s3_2711,a784,s3_2976,s3_253,a785,a786,a787,a788,a789,a790,a791,a792,s3_255,a793,a794,a795,a796,s3_199,a797,a798,a799,s3_3410,a800,s3_274,a801,a802,a803,s3_230,s3_33,a804,a805,s3_3366,a806,s3_271,s3_21,s3_1,a807,a808,s3_267,a809,s3_272,s3_249,s3_203,a810,s3_266,s3_252,s3_251,s3_247,s3_248,s3_246,s3_243,a811,a812,a813,s3_244,a814,a815,s3_273,s3_254,a816,a817,s3_268,s3_241,a818,a819,a820,s3_242,a821,a822,s3_257,s3_235,a823,a824,s3_261,s3_231,s3_240,s3_269,s3_234]) (PetersenIndexedNode.reasons 256 17 498 0x200a10049420240099404084048027108088405004d31111888a009e6222311140130840442027030108088404a020614128081c0c0c282503028080840442028025c0128420300265040084054041004a5010401254100a08080244011d084862225040188888404e0c0210118889c18062222101282008405004528201410200887060383040118e0c07060802194100a080b03028202c0814040908050102c0c12100a0305010141014040501048401400084045040280014040a08050102101242008405004128201410141007060383040108e0c07060504014100a081003f242012102007c282014104010050402820801e921009081003b14100a0814040c8c05010400f19180c8c050100a08050404808141012000840448402400120209080480821010a0808404a8882420121014100282014102a220504028205040121009080988814100a080a08038301c10262207060283028200a0805041003903010180a007026221311400e84c442622801b818080c04a424030101809404084805010290910900a0245010018080c044c0c0301018088404c4c02101130318980480c2101018080c050035030101809410026221311400d84c4426225040018080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c0500348019c00ca005226241312400c6000d00305111098914440a02041c0a8081444483815011280804c48a02021010989084044808313012020840462602101120204c484808514120e054500a080131209891450426241312282010702a0804941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260801700c080605002d109008482005e21201090400b006040302801500c080604a02041c1280820056838241c12808006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c0907020302018109890424021208014c00a2004f0026800240096004900238011280820008a02021014008084044808800f9202084050021210112022003c4808800ec00720036a080800228202002f0016800a9410200285040800d4006600305040800994102001f000e80068a082001828208009400460020282080058a0800c05000903010988a001026220301400280c04262280038988a000d000501808989200080301018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_201 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_200 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2662 theta)
    · exact b3_2711 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_19 theta)
    · exact b3_2976 theta
    · exact b3_253 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_201 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_200 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2662 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2711 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_202 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_199 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2661 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2660 theta)
    · exact b3_255 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3410 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2712 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_274 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_202 theta)
    · exact b3_199 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2661 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2660 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_255 theta)
    · exact b3_3410 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2712 theta)
    · exact b3_274 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3366 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3090 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_271 theta)
    · exact b3_230 theta
    · exact b3_33 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2987 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2993 theta)
    · exact b3_3366 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_3090 theta)
    · exact b3_271 theta
    · exact b3_21 theta
    · exact b3_1 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3330 theta)
    · exact b3_267 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_243 theta)
    · exact b3_272 theta
    · exact b3_249 theta
    · exact b3_203 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_244 theta)
    · exact b3_266 theta
    · exact b3_252 theta
    · exact b3_251 theta
    · exact b3_247 theta
    · exact b3_248 theta
    · exact b3_246 theta
    · exact b3_243 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_272 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_249 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_203 theta)
    · exact b3_244 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_266 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_241 theta)
    · exact b3_273 theta
    · exact b3_254 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_204 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_242 theta)
    · exact b3_268 theta
    · exact b3_241 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_273 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_254 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_204 theta)
    · exact b3_242 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_268 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_257 theta)
    · exact b3_257 theta
    · exact b3_235 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_235 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_234 theta)
    · exact b3_261 theta
    · exact b3_231 theta
    · exact b3_240 theta
    · exact b3_269 theta
    · exact b3_234 theta
theorem b2_22 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_22 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_22 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons pc34w56 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_23 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_23 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s2_23 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_24 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_24 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true))] s2_24 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_25 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_25 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true))] s2_25 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_26 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_26 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true))] s2_26 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_27 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_27 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true))] s2_27 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_28 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_28 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_28 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w74 (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_29 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_29 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true))] s2_29 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w74 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b2_30 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_30 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true))] s2_30 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w77 (PetersenWireProjection.cons pc32w76 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_31 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_31 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true))] s2_31 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w77 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b2_32 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_32 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true))] s2_32 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xf0f00000f0f00000f0f00000f0f0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w80 (PetersenWireProjection.cons pc32w79 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_33 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_33 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true))] s2_33 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w80 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b2_34 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_34 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_34 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_35 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_35 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_35 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_36 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_36 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s2_36 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_37 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_37 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_37 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_38 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_38 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true))] s2_38 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_39 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_39 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_39 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_40 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_40 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_40 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_41 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_41 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s2_41 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
