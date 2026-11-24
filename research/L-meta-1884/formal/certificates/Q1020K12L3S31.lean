import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S5
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S41
import Q1020K12L4S43
import Q1020K12L4S44
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S48
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc34w9 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w8 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w9 stored19 rfl rfl
private theorem pc34w10 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w11 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w14 stored19 rfl rfl
private theorem pc34w16 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w15 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w12 pc34w16 rfl rfl


private theorem pc41w17 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl






private theorem pc41w26 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 1 stored91 stored92 rfl rfl
private theorem pc41w28 : PetersenPackedPin.project extra41 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 1 stored89 stored92 rfl rfl
private theorem pc41w25 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 3 pc41w26 pc41w28 rfl rfl
private theorem pc41w29 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored90 rfl rfl








private theorem pc32w39 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored28 stored29 rfl rfl
private theorem pc32w38 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc000000000000000000cc00cc00cc00cc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc32w39 stored25 rfl rfl
private theorem pc32w40 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl
private theorem pc32w41 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w42 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc32w41 stored28 rfl rfl



private theorem pc2w44 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl





private theorem pc2w52 : PetersenPackedPin.project cycle2 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored42 stored45 rfl rfl
private theorem pc2w54 : PetersenPackedPin.project cycle2 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored43 stored45 rfl rfl
private theorem pc2w51 : PetersenPackedPin.project cycle2 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w52 pc2w54 rfl rfl
private theorem pc2w55 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc32w56 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w57 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored28 rfl rfl
private theorem pc32w59 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored24 stored29 rfl rfl
private theorem pc32w58 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 1 pc32w59 stored28 rfl rfl
private theorem pc32w61 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored28 rfl rfl
private theorem pc32w60 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w57 pc32w61 rfl rfl








private theorem pc26w71 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0x2222222222222222aaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w71 pc26w72 rfl rfl
private theorem pc26w73 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl






private theorem pc30w81 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl


private theorem pc30w83 : PetersenPackedPin.project extra30 (0x3030303030303030f0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w81 stored13 rfl rfl
private theorem pc30w85 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl






private theorem pc0w92 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl


private theorem pc0w94 : PetersenPackedPin.project cycle0 (0x3333333300000000ffffffff000000003333333300000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc0w92 stored51 rfl rfl
private theorem pc0w96 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc2w98 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w97 : PetersenPackedPin.project cycle2 (0x3333333300000000ffffffff000000003333333300000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w98 stored43 rfl rfl
private theorem pc0w99 : PetersenPackedPin.project cycle0 (0x3333333333333333ffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 2 pc0w92 stored49 rfl rfl







private theorem pc1w108 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl

private theorem pc1w107 : PetersenPackedPin.project cycle1 (0x3333333333333333ffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc1w108 stored57 rfl rfl
private theorem pc1w110 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 stored57 stored59 rfl rfl
private theorem pc26w112 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0x8888888888888888000000000000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w112 stored1 rfl rfl
private theorem pc26w113 : PetersenPackedPin.project extra26 (0x8888888888888888aaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w71 pc26w112 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w114 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa2222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w115 pc26w72 rfl rfl
private theorem pc26w116 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w115 pc26w112 rfl rfl
private theorem pc26w118 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w117 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w118 pc26w71 rfl rfl
private theorem pc26w119 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w118 pc26w72 rfl rfl
private theorem pc26w120 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w118 pc26w112 rfl rfl
private theorem pc26w121 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w118 pc26w115 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w122 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 pc26w123 pc26w124 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 pc26w123 pc26w126 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 pc26w128 pc26w124 rfl rfl
private theorem pc26w130 : PetersenPackedPin.project extra26 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored6 stored7 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 pc26w126 pc26w130 rfl rfl
private theorem pc30w132 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl
private theorem pc30w131 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w132 stored9 rfl rfl
private theorem pc30w134 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w133 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w134 stored13 rfl rfl
private theorem pc34w136 : PetersenPackedPin.project extra34 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored17 stored22 rfl rfl
private theorem pc34w135 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000ffff0000ffff0000cccc0000cccc0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc34w136 stored19 rfl rfl
private theorem pc0w138 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w137 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w138 stored50 rfl rfl
theorem b3_1302 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1302 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(1,true))] s3_1302 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w10 (PetersenWireProjection.cons pc34w8 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1303 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1303 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_1303 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w10 (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w11 rfl)))))))))) (by decide +kernel)
theorem b3_1304 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1304 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_1304 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w10 (PetersenWireProjection.cons pc34w13 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1305 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1305 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_1305 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w10 (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1306 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1306 := by
  apply PetersenIndexedNode.close (bank := [s4_241,a4382,a4383,s4_1834,s4_423,a4384,a4385,s4_1875,s4_501,a4386,s4_1920,s4_1933,s4_849,a4387,s4_1965,s4_1981,a4388,s4_314,a4389,a4390,s4_1,a4391,s4_935,a4392,a4393,s4_2027,s4_2034,a4394,s4_938,s4_923,a4395,a4396,s4_939,s4_906,s4_905]) (PetersenIndexedNode.reasons 256 17 417 0xc4442800140012000c28248003111185048444480014000a00100228010ac0020038a080504024002002c9000381028200e0405000706014000e040e0c0381014001410050004c040a081300090006460240013010c8c0480424000504090002c040a080b0005000242014000b0104840280414000504050005444121009080a08014100a08151102820141028200908048404a020180928009000424024001280884804802240000c0490002a0201808a8005000626014000a808c4c02802140000c045000800f818080c04a08013110988a004026221311282000c0406021612018080c04282007050380858480e0a03050a0800c040602490100c052400900041c0a40012404838148012400006029000290100c04a4005000212014000a404424028011400006025000514100c040602a0801312098914504262413122820006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301488080c092200900041c124001220283824800a400006049000288080c08a200500030b014000a20261602800940000604500050c080c080604a080109008481430221201090282000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c0006020302018081810424006046222141010808900048402400188889080682024000a0809000614124200840450002820140018504504028201400121005000504014100a081001e38301c18141007060383040074a0805040242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060221201410084800301494100c0484809282212000c04a080030130b014100a080030228a080c08c2c0514128a000c08a0800302800e4006d60409000800a24000e041001938101400200305000381040068e0405000800b94002002d00151080a8202002821011410400485040484080089210050410013141012102002048401311400384c4406028006818084c45000f13110180a001806021312400284c480301800480c044c49000b131200c060010030110904001842400302800280c0842410007109000c0a00080302383040008e0c05040800094100e0c1000338301410200005040)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_241 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_884 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1756 theta)
    · exact b4_1834 theta
    · exact b4_423 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_316 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1868 theta)
    · exact b4_1875 theta
    · exact b4_501 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_80 theta)
    · exact b4_1920 theta
    · exact b4_1933 theta
    · exact b4_849 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_243 theta)
    · exact b4_1965 theta
    · exact b4_1981 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_424 theta)
    · exact b4_314 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1961 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1982 theta)
    · exact b4_1 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1911 theta)
    · exact b4_935 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_503 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_73 theta)
    · exact b4_2027 theta
    · exact b4_2034 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2048 theta)
    · exact b4_938 theta
    · exact b4_923 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_361 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_924 theta)
    · exact b4_939 theta
    · exact b4_906 theta
    · exact b4_905 theta
theorem b3_1307 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1307 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1307 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000ffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w29 (PetersenWireProjection.cons pc41w25 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w17 rfl)))))))))) (by decide +kernel)
theorem b3_1308 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1308 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(5,false),(1,false))] s3_1308 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w38 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1309 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1309 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(5,true),(1,true))] s3_1309 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w39 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w41 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1310 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1310 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(5,true),(1,true))] s3_1310 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1311 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1311 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1311 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w55 (PetersenWireProjection.cons pc2w51 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w44 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1312 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1312 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1312 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w55 (PetersenWireProjection.cons pc2w51 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1313 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1313 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(5,true),(3,true))] s3_1313 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w57 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w56 rfl)))))))))) (by decide +kernel)
theorem b3_1314 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1314 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(1,true),(3,true))] s3_1314 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w58 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1315 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1315 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,true)),(false,(5,true),(3,true))] s3_1315 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w40 (PetersenWireProjection.cons pc32w60 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1316 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1316 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1316 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1317 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1317 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,false),(1,false))] s3_1317 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1318 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1318 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1318 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1319 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1319 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,false),(3,false))] s3_1319 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1320 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1320 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1320 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1321 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1321 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1321 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1322 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1322 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1322 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xffff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w96 (PetersenWireProjection.cons pc0w94 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w92 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1323 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1323 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1323 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w55 (PetersenWireProjection.cons pc2w97 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1324 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1324 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1324 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w55 (PetersenWireProjection.cons pc2w97 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1325 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1325 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1325 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0] (PetersenWireProjection.cons pc0w96 (PetersenWireProjection.cons pc0w99 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w92 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 rfl)))))))))) (by decide +kernel)
theorem b3_1326 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1326 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1326 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc1w110 (PetersenWireProjection.cons pc1w107 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 rfl))))))))) (by decide +kernel)
theorem b3_1327 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1327 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1327 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w110 (PetersenWireProjection.cons pc1w107 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1328 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1328 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1328 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w111 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1329 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1329 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1329 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w113 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1330 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1330 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1330 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w114 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1331 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1331 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1331 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w116 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1332 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1332 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1332 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w117 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1333 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1333 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1333 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w119 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1334 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1334 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1334 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1335 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1335 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s3_1335 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons pc26w121 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1336 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1336 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,false),(3,true))] s3_1336 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xf0f00000f0f00000f0f00000f0f0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w122 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1337 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1337 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(7,false),(3,true))] s3_1337 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w125 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1338 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1338 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(7,false),(3,true))] s3_1338 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0x55550000555500005555000055550000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1339 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1339 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true)),(false,(7,false),(3,true))] s3_1339 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0000000000000000,0x0,0xaaaa0000aaaa0000aaaa0000aaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1340 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1340 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1340 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w131 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1341 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1341 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true))] s3_1341 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w85 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w133 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1342 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1342 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true))] s3_1342 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w10 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w135 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1343 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1343 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s3_1343 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff0000,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w96 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w137 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
