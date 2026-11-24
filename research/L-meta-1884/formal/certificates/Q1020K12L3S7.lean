import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc34w3 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl





private theorem pc34w10 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w9 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w10 stored16 rfl rfl
private theorem pc34w11 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w14 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w16 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w15 : PetersenPackedPin.project extra34 (0xffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc34w16 stored16 rfl rfl
private theorem pc34w17 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored16 stored17 rfl rfl
private theorem pc34w18 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored17 stored22 rfl rfl
private theorem pc34w19 : PetersenPackedPin.project extra34 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored17 stored22 rfl rfl
private theorem pc34w20 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w21 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w22 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl



private theorem pc1w26 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl

private theorem pc1w28 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w25 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w26 pc1w28 rfl rfl




private theorem pc1w35 : PetersenPackedPin.project cycle1 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored59 stored60 rfl rfl
private theorem pc1w34 : PetersenPackedPin.project cycle1 (0xffff000000000000ffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 pc1w35 stored57 rfl rfl
private theorem pc34w37 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w36 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc34w37 stored16 rfl rfl
private theorem pc34w39 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffff0000cccc0000ffff0000cccc : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 2 pc34w39 pc34w37 rfl rfl
private theorem pc34w41 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 pc34w41 stored16 rfl rfl
private theorem pc34w42 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w43 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored18 stored22 rfl rfl








private theorem pc0w52 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w54 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w51 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w52 pc0w54 rfl rfl
private theorem pc0w55 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc0w54 stored49 rfl rfl
private theorem pc0w56 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored18 stored22 rfl rfl
private theorem pc34w58 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w21 stored16 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 2 pc34w39 pc34w21 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc34w11 stored16 rfl rfl
private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 2 pc34w39 pc34w11 rfl rfl




private theorem pc32w65 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl




private theorem pc32w72 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w74 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored28 stored29 rfl rfl
private theorem pc32w73 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w74 stored24 rfl rfl
private theorem pc32w75 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl
private theorem pc32w76 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored24 stored25 rfl rfl
private theorem pc32w77 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 stored25 stored26 rfl rfl
private theorem pc32w78 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored26 rfl rfl
private theorem pc32w79 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored25 stored26 rfl rfl
private theorem pc32w80 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w81 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
theorem b3_294 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_294 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,false),(5,false))] s3_294 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w3 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_295 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_295 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(5,true))] s3_295 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w11 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_296 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_296 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(7,true))] s3_296 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w12 rfl)))))))))) (by decide +kernel)
theorem b3_297 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_297 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(5,true),(7,true))] s3_297 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w13 rfl)))))))))) (by decide +kernel)
theorem b3_298 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_298 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,false),(7,true))] s3_298 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons pc34w14 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_299 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_299 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,false),(7,true))] s3_299 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_300 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_300 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,false),(5,true))] s3_300 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xaaaa0000aaaa0000aaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons pc34w18 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_301 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_301 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,false),(1,true))] s3_301 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0x55550000555500005555000055550000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons pc34w19 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_302 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_302 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,false),(1,false))] s3_302 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w20 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_303 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_303 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(1,true))] s3_303 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w21 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_304 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_304 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_304 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w22 rfl)))))))))) (by decide +kernel)
theorem b3_305 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_305 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_305 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w13 rfl)))))))))) (by decide +kernel)
theorem b3_306 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_306 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_306 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w34 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w25 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_307 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_307 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_307 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons pc34w36 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_308 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_308 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_308 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w37 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_309 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_309 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_309 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfafafafafafafafa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_310 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_310 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(1,false),(7,true))] s3_310 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w14 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_311 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_311 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,false),(7,true))] s3_311 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w42 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_312 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_312 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(5,true),(3,true))] s3_312 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w11 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_313 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_313 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,true),(1,false))] s3_313 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w43 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_314 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_314 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_314 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w55 (PetersenWireProjection.cons pc0w51 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_315 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_315 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_315 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons pc0w55 (PetersenWireProjection.cons pc0w51 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w56 rfl)))))))))) (by decide +kernel)
theorem b3_316 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_316 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_316 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w55 (PetersenWireProjection.cons pc0w51 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w56 rfl))))))))) (by decide +kernel)
theorem b3_317 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_317 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,false),(1,true))] s3_317 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0x50505050505050505050505050505050,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_318 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_318 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,false),(1,false))] s3_318 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w58 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_319 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_319 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,true),(1,true))] s3_319 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w37 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_320 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_320 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(1,true),(7,true))] s3_320 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w22 rfl)))))))))) (by decide +kernel)
theorem b3_321 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_321 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(3,true),(7,true))] s3_321 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w12 rfl)))))))))) (by decide +kernel)
theorem b3_322 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_322 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_322 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_323 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_323 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_323 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w21 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_324 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_324 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_324 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_325 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_325 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(0,true),(7,true))] s3_325 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffff0f0fffff0f0,0xfffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons pc34w61 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_326 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_326 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(0,true),(7,true))] s3_326 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w11 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_327 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_327 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(0,true),(7,true))] s3_327 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_328 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_328 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_328 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons pc32w72 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w65 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_329 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_329 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,false),(3,true))] s3_329 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xf0f0f0f0f0f0f0f0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons pc32w75 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_330 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_330 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(5,false),(3,true))] s3_330 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xf0f00000f0f00000f0f00000f0f0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons pc32w76 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_331 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_331 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,false),(5,true))] s3_331 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffff0000ffff0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons pc32w77 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_332 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_332 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,false))] s3_332 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons pc32w78 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_333 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_333 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,false),(5,false))] s3_333 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff00000000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w79 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_334 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_334 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true))] s3_334 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w80 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_335 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_335 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(3,true))] s3_335 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w73 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w81 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
