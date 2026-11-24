import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S12
import Q1020K12L4S14
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S30
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S41
import Q1020K12L4S43
import Q1020K12L4S44
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S48
import Q1020K12L4S49
import Q1020K12L4S50
import Q1020K12L4S53
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S67
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc26w7 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl

private theorem pc26w9 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w9 pc26w11 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w15 stored0 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored3 stored7 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w14 pc26w16 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w19 pc26w17 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w22 stored0 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 1 stored3 stored7 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 1 pc26w21 pc26w23 rfl rfl






private theorem pc30w30 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl


private theorem pc30w33 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w35 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w32 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w33 pc30w35 rfl rfl
private theorem pc30w36 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl






private theorem pc32w43 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl


private theorem pc32w46 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w48 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w45 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc32w46 pc32w48 rfl rfl
private theorem pc32w49 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl


private theorem pc74w50 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl




private theorem pc74w59 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored114 stored119 rfl rfl
private theorem pc74w58 : PetersenPackedPin.project extra74 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w59 stored113 rfl rfl

private theorem pc74w60 : PetersenPackedPin.project extra74 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored116 stored119 rfl rfl
private theorem pc74w57 : PetersenPackedPin.project extra74 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w58 pc74w60 rfl rfl

private theorem pc74w64 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored116 rfl rfl
private theorem pc74w65 : PetersenPackedPin.project extra74 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored114 stored116 rfl rfl
private theorem pc74w63 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc74w64 pc74w65 rfl rfl







private theorem pc34w73 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w77 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w75 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w76 pc34w77 rfl rfl
private theorem pc74w78 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl






private theorem pc0w85 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl


private theorem pc0w88 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w90 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w87 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w88 pc0w90 rfl rfl
private theorem pc0w91 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl






private theorem pc1w98 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl


private theorem pc1w101 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w103 : PetersenPackedPin.project cycle1 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored58 stored60 rfl rfl
private theorem pc1w100 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w101 pc1w103 rfl rfl
private theorem pc1w104 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w107 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w105 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc34w106 pc34w107 rfl rfl
private theorem pc74w109 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored113 stored119 rfl rfl
private theorem pc74w110 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl
private theorem pc74w108 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w109 pc74w110 rfl rfl


private theorem pc107w111 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored161 stored162 rfl rfl




private theorem pc107w119 : PetersenPackedPin.project extra107 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored166 rfl rfl
private theorem pc107w118 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w119 stored161 rfl rfl

private theorem pc107w121 : PetersenPackedPin.project extra107 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored167 stored166 rfl rfl
private theorem pc107w117 : PetersenPackedPin.project extra107 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w118 pc107w121 rfl rfl

private theorem pc107w125 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored161 stored167 rfl rfl
private theorem pc107w126 : PetersenPackedPin.project extra107 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored162 stored167 rfl rfl
private theorem pc107w124 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w125 pc107w126 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc30w128 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored12 stored13 rfl rfl
private theorem pc30w131 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w130 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w131 stored8 rfl rfl
private theorem pc30w132 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w129 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w130 pc30w132 rfl rfl
private theorem pc30w133 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w134 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w135 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w134 pc30w133 rfl rfl
private theorem pc30w138 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w137 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w138 stored8 rfl rfl
private theorem pc30w139 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored11 stored13 rfl rfl
private theorem pc30w136 : PetersenPackedPin.project extra30 (0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 1 pc30w137 pc30w139 rfl rfl
theorem b3_2226 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2226 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2226 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w7 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2227 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2227 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2227 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w7 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2228 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2228 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2228 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2229 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2229 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2229 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2230 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2230 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2230 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2231 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2231 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2231 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2232 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2232 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2232 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2233 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2233 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2233 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2234 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2234 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2234 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x32323232323232323232323232323232,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2235 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2235 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2235 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x32323232323232323232323232323232,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2236 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2236 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2236 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w30 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2237 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2237 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2237 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w30 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2238 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2238 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s3_2238 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w43 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_2239 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2239 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s3_2239 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w45 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w43 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w49 rfl)))))))))) (by decide +kernel)
theorem b3_2240 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2240 := by
  apply PetersenIndexedNode.close (bank := [s4_1,a4998,s4_1945,s4_1435,a4999,a5000,s4_1851,a5001,a5002,s4_1946,s4_1438,s4_1881,a5003,a5004,s4_1995,s4_1891,a5005,a5006,s4_2000,s4_1897,a5007,a5008,a5009,s4_1898,a5010,a5011,s4_2045,s4_1899,s4_497,a5012,a5013]) (PetersenIndexedNode.reasons 256 17 417 0xc4442800140012000c28248003111185048444480014000a000b0201080ac0012000a08048002c081410090204800084052000702010809c000a000614128001c080c2825020280008404a00098081410260012000c8c04800260219180900848000a08120005808141016000a00048402800160209080500828000a080a000280824200a0004202282014000a0205040280810809210042029404030125001200084804800250110900900448000180920005404030115000a000c4c028001501189805004280001808a0002505030109404420226221080894144c44210510808180842022c2403010180850400e0a07010b0901c14060a1410018080c04920221202480920008381480024809070292024800109012000520241c094808a000424028001480884805202280020e04a0002a0a21200a8284202626010808a828c4c02a0a10809090042022a2221200a88850408b8914100a88917122a2214101090050400602212001809090046442320018088c88060242401090084809202800ea48092001001c48002480a003c920248004006d20005202800c94808a001001828001480a0034520228004005ca0002a0a800a8a8284203001410808a82a002c2a0a1080c004c42022a2280088a8885041001014100a88a00242a2214104003c504006028006818090901000c42400180a001c060242404002d09010003800500c04848100000180a440406049100480020e092000910141c1240052000030248001440406045100280018580a000510130b014004a000030228000840406042100140408480420021011090084045010030201811250406040302141002c2816044941058500c2850400302018121604060403020301094900c0485811292084900c040302018110d0442402120212000c0806044341018100c088480212010904002042402120800380c0806050009018100c0a000c2120109031110a08084044800242012000c44448403410120005040480030a0921004808280014100a000c282282014100a0009080280018504a080504010809c1804202614138301c10042025040108092100a0804840141026220504048404c441210050405040141021200a08050400301151100c0484802a22151000c045040030140016000890822120400048481000328201410200050001494140000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2590 theta)
    · exact b4_1945 theta
    · exact b4_1435 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_388 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_369 theta)
    · exact b4_1851 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1394 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1392 theta)
    · exact b4_1946 theta
    · exact b4_1438 theta
    · exact b4_1881 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1549 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1572 theta)
    · exact b4_1995 theta
    · exact b4_1891 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1399 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1568 theta)
    · exact b4_2000 theta
    · exact b4_1897 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_475 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1545 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2016 theta)
    · exact b4_1898 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_884 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1837 theta)
    · exact b4_2045 theta
    · exact b4_1899 theta
    · exact b4_497 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1836 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2055 theta)
theorem b3_2241 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2241 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2241 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc74w63 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w57 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w50 rfl)))))))))) (by decide +kernel)
theorem b3_2242 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2242 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(5,true),(7,true))] s3_2242 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w75 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w73 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2243 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2243 := by
  apply PetersenIndexedNode.close (bank := [s4_1401,a5014,a5015,a5016,s4_1897,s4_2838,s4_2612,s4_1940,s4_1852,a5017,a5018,s4_1947,s4_1,a5019,a5020,s4_1882,a5021,a5022,s4_1996,a5023,a5024,a5025,a5026,a5027,a5028,s4_1904,a5029,a5030,s4_2046,a5031,s4_501,a5032,a5033,a5034,s4_1907]) (PetersenIndexedNode.reasons 256 17 417 0xc4442800140012000c28248003111185048444480014000a000b0201080ac0012000a08048002c081410090204800084052000702010809c000a000614128001c080c2825020280008404a00098081410260012000c8c04800260219180900848000a08120005808141016000a00048402800160209080500828000a080a000280824200a0004202282014000a0205040280810809210042029404030125001200084804800250110900900448000180920005404030115000a000c4c028001501189805004280001808a0002505030109404420226221080894144c44210510808180842022c2403010180850400e0a07010b0901c14060a1410018080c0492020180a48012000838148002480907029002480000c0520005202018094800a000424028001480884805002280000c04a0010018018080c044203000e1080c008a0042280a151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c0406040301212000602030159114007d64449000800f2400164450020591124002003a900039114006ce4445000800d14000e445001c39111400200325000800c4005c541421018006084045445001515110a082002828201511400585444282080098a0804c45001113110180a002006021311400484c44060280078180a001d000d131200c0600180301488080c092200900041c124001220283824800a400006049000288080c08a200500030b014000a202616028009400006045000108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800500c0806050009119108c8a00162322119140020060403026222141010808900048402400188889080682024000a080900061412420084045000282014001850450402820140012100500030a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060221201410084800301494100c0484809282212000c04a0800301800214100a0810003800140006000f00068002c0000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1401 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1248 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1246 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1243 theta)
    · exact b4_1897 theta
    · exact b4_2838 theta
    · exact b4_2612 theta
    · exact b4_1940 theta
    · exact b4_1852 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1289 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1605 theta)
    · exact b4_1947 theta
    · exact b4_1 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_609 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_607 theta)
    · exact b4_1882 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1432 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1283 theta)
    · exact b4_1996 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1882 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1432 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1283 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1996 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_609 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_607 theta)
    · exact b4_1904 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_501 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1271 theta)
    · exact b4_2046 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1904 theta)
    · exact b4_501 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1271 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2046 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1907 theta)
    · exact b4_1907 theta
theorem b3_2244 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2244 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2244 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc74w63 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w78 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w50 rfl)))))))))) (by decide +kernel)
theorem b3_2245 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2245 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2245 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w87 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w85 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2246 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2246 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2246 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons pc0w87 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w85 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w91 rfl)))))))))) (by decide +kernel)
theorem b3_2247 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2247 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2247 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w100 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w98 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_2248 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2248 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2248 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons pc1w100 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w98 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w104 rfl)))))))))) (by decide +kernel)
theorem b3_2249 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2249 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,true),(1,false))] s3_2249 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w75 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w105 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2250 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2250 := by
  apply PetersenIndexedNode.close (bank := [s4_1438,a4891,s4_1900,s4_1944,s4_1901,s4_1926,s4_1853,a5035,a5036,s4_1948,s4_1,s4_73,s4_72,s4_1883,a5037,a5038,s4_1997,s4_1892,a5039,a5040,a5041,a5042,s4_2102,s4_2001,s4_1925,s4_1905,a5043,a5044,a5045,s4_1911,a5046,a5047,s4_2047,s4_1917,s4_531,a5048,a5049,s4_2078,a5050,s4_1923,a5051,s4_1927,s4_593,s4_1928,s4_1924]) (PetersenIndexedNode.reasons 256 17 426 0x18888500028002400185049000622230a09088890002800140016040210158002400141009000581028201204090001080a4000e0402101380014000c2825000381018504a0405000108094001301028204c0024001918090004c043230120109000141024000b01028202c0014000908050002c0412100a0105000141014000501048401400084045040280014040a08050102101242008405280806024a0024001090090004a022120120089000030124000a80806022a0014001898050002a0231300a00850000301140004a0a06021280884044c442101128289888420a21010301084045848060203010a0801c140e021612038280c14282003010180a004803010180a4002005490008016400ad200490000180a400185040301018094002005050006141400a4a0045000018094000541403010180884044c48210115050989050142101018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c0600490023490124002004490008013c009a004a90008010a40018505001f290114002003c500061414008185045000800e940014505001b5141084060034210151414007145042101800c88406002b001480098a08200242820800c4005e002c282080088a0810d05000f43410180a001c06024341400410d04060280068180a0019000b212000c0600140301488080c092200900041c124001220283824800a400006049000288080c08a200500030b014000a202616028009400006045000108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800400c080605000741c120e0a0012838241c140018060403026222141010808900048402400188889080682024000a080900061412420090105000282014001850450402820140012100500030a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a0800602800214100a0800301494100c06000a9282494100c04a0800301800114100a0810001494124a0a00069282494140000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1438 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_370 theta)
    · exact b4_1900 theta
    · exact b4_1944 theta
    · exact b4_1901 theta
    · exact b4_1926 theta
    · exact b4_1853 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1198 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1576 theta)
    · exact b4_1948 theta
    · exact b4_1 theta
    · exact b4_73 theta
    · exact b4_72 theta
    · exact b4_1883 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1617 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1201 theta)
    · exact b4_1997 theta
    · exact b4_1892 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1428 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1188 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1186 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1187 theta)
    · exact b4_2102 theta
    · exact b4_2001 theta
    · exact b4_1925 theta
    · exact b4_1905 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_545 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1191 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2021 theta)
    · exact b4_1911 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_503 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_945 theta)
    · exact b4_2047 theta
    · exact b4_1917 theta
    · exact b4_531 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_674 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_677 theta)
    · exact b4_2078 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2056 theta)
    · exact b4_1923 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_936 theta)
    · exact b4_1927 theta
    · exact b4_593 theta
    · exact b4_1928 theta
    · exact b4_1924 theta
theorem b3_2251 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2251 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2251 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc74w63 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w108 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w50 rfl)))))))))) (by decide +kernel)
theorem b3_2252 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2252 := by
  apply PetersenIndexedNode.close (bank := [a5052,s4_2581,s4_1446,s4_1441,a5053,a4998,s4_1,s4_1902,a5054,a5055,a5056,s4_2844,a5057,s4_2845,a5058,a5059,s4_1857,a5060,a5061,s4_1950,a4891,s4_1890,s4_1889,s4_1888,a5062,a5063,a5064,a5065,s4_1999,s4_1896,a5066,a5067,s4_2003,a5068,a5069,a5070,s4_2023,s4_1942,a5071,a5072,s4_2049,s4_1943,s4_841,a5073,a5074]) (PetersenIndexedNode.reasons 256 17 417 0xc4442800140012000c28248003111185048444480014000a000b0201080ac0012000a08048002c081410090204800084052000702010809c000a000614128001c080c2825020280008404a00098081410260012000c8c04800260219180900848000a08120005808141016000a00048402800160209080500828000a080a000280824200a0004202282014000a0205040280810809210042029404030125001200084804800250110900900448000180920005404030115000a000c4c028001501189805004280001808a0002505030109404420226221080894144c44210510808180842022c2403010180850400e0a07010b0901c14060a1410018080c0492028015a48092001002a48002480a005892024800400a520005202801394808a001002628001480a00505202280040094a0002a0a80118a8284203002210808a82a00482a0a1080c008442022a22800f8a8885041001e14100a88a00402a2214104007450400602800d8180a00350019800c0180a00380602800bc005a002a920221202480920008381480024809070292024800109012000520241c094808a000424028001480884805202280020e04a0002a0a21200a8284202626010808a828c4c02a0a10809090042022a2221200a88850408b8914100a88917122a2214101090050400602212001809090046442320018088c88060242401090084810014800200c06000c42400180a440406049100480020e092000910141c1240052000030248001440406045100280018580a000510130b014004a000030228000840406042100140408480420021011090084045010030201811250406040302141002c2816044941058500c2850400302018121604060403020301094900c0485811292084900c04030201814004842402120800880c0806050013018100c0a00202120109010d0442402120212000c0806044341018100c0884802120109031112001ea222480024a092000c4444941311112001000e480030a0925044202280040030a000c2828006b0a08a0009282280018505250461411080c0028420261418005985044202928210809210125044840141026a28504048404d451210050409282141021201250484800301400200c0484808004a12000c04928203014001e000a5040800324a08a08042408002909020008928249414000e0004524030b024a08c2c00302800000c08c2c1000130b000c0925040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1379 theta)
    · exact b4_2581 theta
    · exact b4_1446 theta
    · exact b4_1441 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_371 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2590 theta)
    · exact b4_1 theta
    · exact b4_1902 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1371 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2586 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_380 theta)
    · exact b4_2844 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_266 theta)
    · exact b4_2845 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1659 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2266 theta)
    · exact b4_1857 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_422 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1758 theta)
    · exact b4_1950 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_370 theta)
    · exact b4_1890 theta
    · exact b4_1889 theta
    · exact b4_1888 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1753 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1751 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1752 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_420 theta)
    · exact b4_1999 theta
    · exact b4_1896 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1546 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_421 theta)
    · exact b4_2003 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1909 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_842 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_475 theta)
    · exact b4_2023 theta
    · exact b4_1942 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1010 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_425 theta)
    · exact b4_2049 theta
    · exact b4_1943 theta
    · exact b4_841 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_411 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2058 theta)
theorem b3_2253 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2253 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s3_2253 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xffffffffffffffff,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc107w124 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons pc107w117 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 (PetersenWireProjection.cons pc107w111 rfl)))))))))) (by decide +kernel)
theorem b3_2254 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2254 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2254 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2255 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2255 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2255 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2256 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2256 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2256 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w128 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2257 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2257 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2257 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w128 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2258 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2258 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2258 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w129 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2259 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2259 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2259 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w129 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2260 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2260 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2260 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w133 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2261 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2261 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2261 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w133 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2262 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2262 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2262 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w134 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2263 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2263 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2263 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w134 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2264 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2264 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2264 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w135 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2265 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2265 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2265 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w135 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
theorem b3_2266 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2266 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2266 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfffffffff0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2267 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2267 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2267 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfffffffff0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w32 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w36 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
