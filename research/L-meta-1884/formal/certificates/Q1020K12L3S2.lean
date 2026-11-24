import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S28
import Q1020K12L4S43
import Q1020K12L4S44
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S48
import Q1020K12L4S53
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w8 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 pc3w9 stored34 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w11 stored33 rfl rfl
private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl








private theorem pc0w21 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored51 rfl rfl
private theorem pc0w23 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w22 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 pc0w23 stored49 rfl rfl


private theorem pc116w24 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored106 rfl rfl






private theorem pc116w33 : PetersenPackedPin.project extra116 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored106 stored107 rfl rfl
private theorem pc116w35 : PetersenPackedPin.project extra116 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored106 stored111 rfl rfl
private theorem pc116w34 : PetersenPackedPin.project extra116 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc116w35 stored105 rfl rfl








private theorem pc1w44 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored59 rfl rfl
private theorem pc1w46 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 stored58 stored63 rfl rfl
private theorem pc1w45 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 1 pc1w46 stored57 rfl rfl
private theorem pc116w48 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored105 stored107 rfl rfl
private theorem pc116w47 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc116w48 pc116w33 rfl rfl


private theorem pc34w49 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl






private theorem pc34w57 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored17 stored22 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xcccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa := PetersenWireProjection.derive 1 pc34w60 stored16 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w63 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w62 pc34w61 rfl rfl


private theorem pc39w64 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl






private theorem pc39w73 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w75 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored74 stored76 rfl rfl
private theorem pc39w72 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w73 pc39w75 rfl rfl
private theorem pc39w77 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored74 stored79 rfl rfl
private theorem pc39w76 : PetersenPackedPin.project extra39 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc39w77 stored73 rfl rfl


private theorem pc32w78 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl






private theorem pc32w87 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored28 rfl rfl
private theorem pc32w89 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored25 stored29 rfl rfl
private theorem pc32w88 : PetersenPackedPin.project extra32 (0xcccccccccccccccc : BitVec 256) = 0xa0a00000a0a00000a0a00000a0a := PetersenWireProjection.derive 1 pc32w89 stored24 rfl rfl
private theorem pc32w91 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored28 rfl rfl
private theorem pc32w90 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w87 pc32w91 rfl rfl


private theorem pc30w92 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl






private theorem pc30w101 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored13 rfl rfl
private theorem pc30w103 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w102 : PetersenPackedPin.project extra30 (0xcccccccccccccccc : BitVec 256) = 0xf000f00000000000f000f00 := PetersenWireProjection.derive 1 pc30w103 stored8 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w104 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w105 pc30w101 rfl rfl
private theorem pc3w106 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333333333333333333330000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w107 pc3w110 rfl rfl
private theorem pc39w112 : PetersenPackedPin.project extra39 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored73 stored79 rfl rfl
private theorem pc39w113 : PetersenPackedPin.project extra39 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff := PetersenWireProjection.derive 1 stored74 stored79 rfl rfl
private theorem pc39w111 : PetersenPackedPin.project extra39 (0x3333333333333333333333333333333333333333333333330000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff := PetersenWireProjection.derive 3 pc39w112 pc39w113 rfl rfl








private theorem pc26w123 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w122 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555555555555555555550000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w123 pc26w124 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xcccccccccccccccc : BitVec 256) = 0x5050000050500000505000005050000 := PetersenWireProjection.derive 1 pc26w126 stored0 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w128 pc26w129 rfl rfl
private theorem pc3w130 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w132 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w133 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w131 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w132 pc3w133 rfl rfl
private theorem pc30w135 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w136 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w134 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w135 pc30w136 rfl rfl
private theorem pc32w138 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w139 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored25 stored28 rfl rfl
private theorem pc32w137 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w138 pc32w139 rfl rfl
private theorem pc34w141 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored16 stored19 rfl rfl
private theorem pc34w142 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored17 stored19 rfl rfl
private theorem pc34w140 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w141 pc34w142 rfl rfl
private theorem pc34w144 : PetersenPackedPin.project extra34 (0xffff0000ffff00003333000033330000ffff0000ffff00003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc34w60 stored19 rfl rfl
private theorem pc34w143 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff00003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w144 pc34w141 rfl rfl
private theorem pc0w145 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl
private theorem pc1w146 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl



private theorem pc69w151 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored97 stored99 rfl rfl
private theorem pc69w152 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored99 rfl rfl
private theorem pc69w150 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff00000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w151 pc69w152 rfl rfl





private theorem pc69w159 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored98 stored100 rfl rfl
private theorem pc69w158 : PetersenPackedPin.project extra69 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w159 stored97 rfl rfl
private theorem pc3w160 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc0w161 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc0w162 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored49 stored50 rfl rfl
private theorem pc1w163 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl
private theorem pc1w164 : PetersenPackedPin.project cycle1 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored58 rfl rfl
private theorem pc3w166 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w165 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w166 stored34 rfl rfl
theorem b3_84 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_84 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true))] s3_84 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w8 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_85 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_85 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true))] s3_85 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w8 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w9 rfl)))))))))) (by decide +kernel)
theorem b3_86 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_86 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_86 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w12 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_87 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_87 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s3_87 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w22 (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_88 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_88 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_88 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc116w34 (PetersenWireProjection.cons pc116w33 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored105 (PetersenWireProjection.cons pc116w24 rfl)))))))))) (by decide +kernel)
theorem b3_89 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_89 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,true))] s3_89 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w45 (PetersenWireProjection.cons pc1w44 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_90 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_90 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_90 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w34 (PetersenWireProjection.cons pc116w47 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl)))))))))) (by decide +kernel)
theorem b3_91 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_91 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_91 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w49 rfl)))))))))) (by decide +kernel)
theorem b3_92 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_92 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_92 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons pc34w61 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w49 rfl)))))))))) (by decide +kernel)
theorem b3_93 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_93 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_93 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w49 rfl)))))))))) (by decide +kernel)
theorem b3_94 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_94 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_94 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_95 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_95 := by
  apply PetersenIndexedNode.close (bank := [s4_1,s4_2245,s4_1832,s4_79,s4_47,s4_44,a4054,s4_1873,s4_1922,s4_72,s4_58,a4055,s4_1973,s4_1978,s4_60,s4_28,a4056,a4057,s4_63,s4_17,a4058,a4059,s4_2033,s4_76,a4060,s4_74,s4_70,s4_68,s4_71,s4_75]) (PetersenIndexedNode.reasons 256 17 408 0x622214000a00090006141240018888c282422224000a0005000581008405600090005040240016040a08048102400042029000381008404e000500030a094000e0406141281014000420250004c040a081300090006460240013010c8c0480424000504090002c040a080b0005000242014000b0104840280414000504050001404121005000210114100a00050102820140408404908021014a020180928009000424024001280884804802240000c0490002a0201808a8005000626014000a808c4c02802140000c0450001282818084a0221011311084044a0a26221082884040c0421011612018080c04282007050380858480e0a03050a0800c040602800e109012400900041c0a4002003a838141c0a400084809000614120e04a400500021201400185044240212014001070250001505109005414210131300840454146260150508404848021011511109005444282045c48a08054448b8915110a080848028200301109000c0484802322119000c04464403012120084804240488080c092200900041c124001220283824800a400006049000288080c08a200500030b014000a202616028009400006045000108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c0886820302018110900424021206222141010808900048402400188889080682024000a080900061412420090105000282014001850450402820140012100500030a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a08006022120141008481001b49412420884809282212040068a080504030b014100a080030228a080c08c2c0514128a000c08a0800302800cc006124049000800024002002f0016290114002000050001505400505414210180098840454150015150508406002421011511400405444282080078a0805445001115110a082001c28200301400300c0484808005a12000c05000d030121202001484808004c002006024240800000c0406050006018108482000a212001814001c060421208002084820007000280009410200005040)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1 theta
    · exact b4_2245 theta
    · exact b4_1832 theta
    · exact b4_79 theta
    · exact b4_47 theta
    · exact b4_44 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1871 theta)
    · exact b4_1873 theta
    · exact b4_1922 theta
    · exact b4_72 theta
    · exact b4_58 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_33 theta)
    · exact b4_1973 theta
    · exact b4_1978 theta
    · exact b4_60 theta
    · exact b4_28 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1972 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1979 theta)
    · exact b4_63 theta
    · exact b4_17 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1930 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1932 theta)
    · exact b4_2033 theta
    · exact b4_76 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2034 theta)
    · exact b4_74 theta
    · exact b4_70 theta
    · exact b4_68 theta
    · exact b4_71 theta
    · exact b4_75 theta
theorem b3_96 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_96 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_96 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w76 (PetersenWireProjection.cons pc39w72 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w64 rfl)))))))))) (by decide +kernel)
theorem b3_97 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_97 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false))] s3_97 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a00000a0a00000a0a00000a0a,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w88 (PetersenWireProjection.cons pc32w87 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w78 rfl)))))))))) (by decide +kernel)
theorem b3_98 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_98 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false))] s3_98 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a00000a0a00000a0a00000a0a,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w88 (PetersenWireProjection.cons pc32w90 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_99 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_99 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false))] s3_99 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf000f00000000000f000f00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w101 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w92 rfl)))))))))) (by decide +kernel)
theorem b3_100 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_100 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false))] s3_100 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf000f00000000000f000f00,0xfffffffff0f0f0f0fffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons pc30w104 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_101 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_101 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_101 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccc,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w106 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_102 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_102 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_102 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w107 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 rfl))))))))) (by decide +kernel)
theorem b3_103 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_103 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_103 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w107 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w108 rfl)))))))))) (by decide +kernel)
theorem b3_104 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_104 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_104 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons pc3w109 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_105 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_105 := by
  apply PetersenIndexedNode.close (bank := [a4061,a4062,s4_94,s4_88,s4_93,a4063,s4_92,a4064,s4_90,s4_69,s4_121]) (PetersenIndexedNode.reasons 256 17 414 0x188884200210020c058504c200622230a090888830121001080144402101510020c054100a20051102820144408301108088404c4402101310010800c28242003110185048440420010809080124205040490020c052100920049082420124208301282020c04a4209080290010800a08042002908141008420420048401080062225040188088404e0c0210118889c18042222101282008405161228204580a0c05918083014584b230106128301141020c04941028202500108009080420025041210084104200141010800501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a0810c080602430020c05090086004302212010c088301030120c048c08060223001080189804200230231300840842000301108004a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180906020302418021811070483004180a0e0906028604018100c0886020302218010800c2c04200218098580840242000181108004202030210800a0204240210010808848042022808018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c0988884240420220c0507028301622220e0584808301212020c0591108381240410800848042006444109008480420041c090800c2824240212008404c4c0210130a098980c4802101212008404a0804240212024a0a00129082282040028a08092822120109009080424021200a08117122820242022e249080282021200a081090042402120018088c8806024240119108c800602212001808c2c04240212000c088682030230b010d0486800302212000c0a00110007490920c040602030180034001484044200018090800541403010180884044c48210115050989050142101018080c060006030101809410026221301800204c4406225040018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c040604060401800848006020300018100c04060221200302018120005000180001090006020301)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym4 fix4 (by decide +kernel) (b4_1204 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1032 theta)
    · exact b4_94 theta
    · exact b4_88 theta
    · exact b4_93 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1090 theta)
    · exact b4_92 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1083 theta)
    · exact b4_90 theta
    · exact b4_69 theta
    · exact b4_121 theta
theorem b3_106 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_106 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_106 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w76 (PetersenWireProjection.cons pc39w111 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w64 rfl)))))))))) (by decide +kernel)
theorem b3_107 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_107 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false))] s3_107 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x5050000050500000505000005050000,0xfafafafafafafafafafafafafafafafa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w125 (PetersenWireProjection.cons pc26w122 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_108 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_108 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false))] s3_108 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x5050000050500000505000005050000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w125 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_109 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_109 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_109 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w130 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_110 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_110 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_110 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_111 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_111 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_111 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_112 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_112 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_112 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w108 rfl)))))))))) (by decide +kernel)
theorem b3_113 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_113 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false))] s3_113 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf000f00000000000f000f00,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w134 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_114 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_114 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false))] s3_114 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a00000a0a00000a0a00000a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w88 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w137 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_115 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_115 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_115 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w140 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_116 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_116 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_116 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w140 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_117 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_117 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_117 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w140 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w49 rfl)))))))))) (by decide +kernel)
theorem b3_118 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_118 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_118 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w143 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w49 rfl)))))))))) (by decide +kernel)
theorem b3_119 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_119 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s3_119 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w22 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w145 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_120 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_120 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,true))] s3_120 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w45 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w146 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_121 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_121 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_121 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w158 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons pc69w150 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_122 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_122 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_122 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w160 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_123 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_123 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,false))] s3_123 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w22 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w162 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w161 rfl)))))))))) (by decide +kernel)
theorem b3_124 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_124 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,false))] s3_124 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xc0c0c0c,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0x0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons pc1w45 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w164 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w163 rfl)))))))))) (by decide +kernel)
theorem b3_125 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_125 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_125 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w10 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w165 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
