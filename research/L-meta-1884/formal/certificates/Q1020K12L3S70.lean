import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S30
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S43
import Q1020K12L4S45
import Q1020K12L4S48
import Q1020K12L4S50
import Q1020K12L4S52
import Q1020K12L4S53
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S71
import Q1020K12L4S74
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc32w2 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl

private theorem pc32w1 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w2 stored25 rfl rfl



private theorem pc32w10 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl
private theorem pc32w11 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl
private theorem pc32w9 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w10 pc32w11 rfl rfl




private theorem pc34w15 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl

private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w15 stored17 rfl rfl



private theorem pc34w23 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w24 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w22 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 3 pc34w23 pc34w24 rfl rfl








private theorem pc3w34 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w35 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w33 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w34 pc3w35 rfl rfl

private theorem pc3w37 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w38 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored33 stored35 rfl rfl
private theorem pc3w39 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl


private theorem pc74w41 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl

private theorem pc74w40 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w41 stored113 rfl rfl




private theorem pc74w50 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl
private theorem pc74w51 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl
private theorem pc74w49 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w50 pc74w51 rfl rfl




private theorem pc26w54 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl

private theorem pc26w57 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl




private theorem pc26w64 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w65 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w63 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xffff0000ffff0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w64 pc26w65 rfl rfl
private theorem pc32w66 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w67 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc74w68 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl
private theorem pc3w69 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl
private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w34 stored35 rfl rfl
private theorem pc3w71 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc34w72 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w35 stored36 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w74 pc3w34 rfl rfl



private theorem pc37w76 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl

private theorem pc37w79 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl



private theorem pc37w85 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored65 stored71 rfl rfl
private theorem pc37w86 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 0 stored66 stored71 rfl rfl
private theorem pc37w84 : PetersenPackedPin.project extra37 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 pc37w85 pc37w86 rfl rfl




private theorem pc39w89 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored75 rfl rfl

private theorem pc39w92 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl



private theorem pc39w98 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 0 stored74 stored79 rfl rfl
private theorem pc39w99 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc0000 := PetersenWireProjection.derive 0 stored75 stored79 rfl rfl
private theorem pc39w97 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 pc39w98 pc39w99 rfl rfl

private theorem pc3w101 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc37w102 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w79 stored65 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w33 pc3w104 rfl rfl



private theorem pc111w106 : PetersenPackedPin.project extra111 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored178 stored179 rfl rfl




private theorem pc111w114 : PetersenPackedPin.project extra111 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored177 stored183 rfl rfl
private theorem pc111w113 : PetersenPackedPin.project extra111 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc111w114 pc111w106 rfl rfl







private theorem pc1w122 : PetersenPackedPin.project cycle1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored62 rfl rfl
private theorem pc1w124 : PetersenPackedPin.project cycle1 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored58 stored62 rfl rfl
private theorem pc1w121 : PetersenPackedPin.project cycle1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 2 pc1w122 pc1w124 rfl rfl

private theorem pc1w126 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl

private theorem pc3w128 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w34 stored38 rfl rfl
private theorem pc3w129 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w130 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w129 stored35 rfl rfl
private theorem pc3w131 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w129 pc3w35 rfl rfl



private theorem pc73w135 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored129 stored131 rfl rfl
private theorem pc73w134 : PetersenPackedPin.project extra73 (0xffffffffffffffff0000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w135 stored130 rfl rfl




private theorem pc73w142 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored129 stored135 rfl rfl
private theorem pc73w143 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored131 stored135 rfl rfl
private theorem pc73w141 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w142 pc73w143 rfl rfl

private theorem pc26w146 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w145 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w146 stored0 rfl rfl
private theorem pc26w148 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w147 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff0000f0f00000f0f00000 := PetersenWireProjection.derive 3 pc26w148 pc26w65 rfl rfl
private theorem pc3w149 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w71 stored33 rfl rfl
private theorem pc32w150 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w2 stored24 rfl rfl
private theorem pc32w152 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored24 stored29 rfl rfl
private theorem pc32w151 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc32w152 pc32w11 rfl rfl
private theorem pc74w154 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored113 stored119 rfl rfl
private theorem pc74w153 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w154 pc74w51 rfl rfl
private theorem pc26w155 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w156 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
theorem b3_2940 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2940 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false))] s3_2940 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w9 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w1 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_2941 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2941 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(0,true),(1,false))] s3_2941 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w22 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w14 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2942 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2942 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2942 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2943 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2943 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2943 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w37 rfl)))))))))) (by decide +kernel)
theorem b3_2944 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2944 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2944 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w38 rfl)))))))))) (by decide +kernel)
theorem b3_2945 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2945 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_2945 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w39 rfl)))))))))) (by decide +kernel)
theorem b3_2946 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2946 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2946 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w49 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w40 rfl)))))))))) (by decide +kernel)
theorem b3_2947 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2947 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false))] s3_2947 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w63 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w57 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2948 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2948 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false))] s3_2948 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w9 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons pc32w66 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_2949 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2949 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2949 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w49 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w41 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w68 rfl)))))))))) (by decide +kernel)
theorem b3_2950 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2950 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2950 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w70 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2951 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2951 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2951 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w70 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2952 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2952 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2952 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2953 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2953 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2953 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2954 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2954 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false))] s3_2954 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w9 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w2 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w66 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_2955 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2955 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(0,true),(1,false))] s3_2955 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w22 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w72 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2956 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2956 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2956 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w73 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2957 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2957 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_2957 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons pc37w84 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons pc37w79 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w76 (PetersenWireProjection.cons stored67 rfl)))))))))) (by decide +kernel)
theorem b3_2958 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2958 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2958 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2959 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2959 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_2959 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons pc39w97 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w92 (PetersenWireProjection.cons pc39w89 (PetersenWireProjection.cons stored73 rfl)))))))))) (by decide +kernel)
theorem b3_2960 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2960 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2960 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w33 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w101 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2961 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2961 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_2961 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons pc37w84 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w76 (PetersenWireProjection.cons pc37w102 (PetersenWireProjection.cons stored67 rfl)))))))))) (by decide +kernel)
theorem b3_2962 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2962 := by
  apply PetersenIndexedNode.close (bank := [s4_2467,a5590,a5591,a5592,a5593,s4_2748,a5594,s4_2742,a5595,a5596,a5597,a5598,a5599,a5600,a5601,a5602,a5603]) (PetersenIndexedNode.reasons 256 17 414 0x1242403010180a101107028301490920e0520248404018080c058888480a24052101191148404622232229068284042405210120021000f240400c049014030150100a029400484045041280094040a0825010210105014840480074003442020301140500c04c444280a140512028c282480a3111185048444480a14050a02920205040480021011210090004808242012020840428202101026229080098080c04a080030109889410006220301484000c04a0249080280112028a0805002280914100a024480a484012028703450401c050a028e0c0280a1c0d1c1805034280a28200a0291818282046022101191808404460632301081884041410210101613000c058080c045040030105848a08006120301800580c04901428202401140489080480224051210090145012141014048501448401401018905040280214050a0805014062424200189131102820141014100706038204c440e0c05060504014100a0810808060242002404109008400420221201080890100301018080c088480030000c040c0406000302018080c040301424000c04e86806020301120298980480a3a1a31300e068480a0301018080c48060203010a0284c44280a0312098880c40280a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018094444262451102101185808404511130b014044840413122101200150009800400c044c4803013111098908404480a212010808c44442403111120284c48480a8003109005414280a13120a02a000e262413120a0288480280a8002098904c4850401b1a0d892000a3634131a141004c4826241511098905440282080010a0805445000314110a0804c4828201311109004c4006021312018084c44262413110180884800602428280c080604840441c120c090a0a83824202a1010060403020180c000406000604018100c00060203020180818120000060401a080c080604480a30b0120280682616001a0120280604030230a080c080604280a109008408c282212001900a0280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a080c0806042624119108c808682232210910989006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2467 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2190 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1447 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2899 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1189 theta)
    · exact b4_2748 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_774 theta)
    · exact b4_2742 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1204 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1206 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1205 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2469 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2136 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1151 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1149 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1089 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1087 theta)
theorem b3_2963 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2963 := by
  apply PetersenIndexedNode.close (bank := [a5604,a5605,s4_2353,a5606,a5607,s4_2745,a5608,s4_2744,a5609,a5610,a5611,s4_2749,a5612,a5613,a5614,a5615,s4_548,a5616,a5617,s4_2746,a5618,a5619,s4_2740,a5620,s4_2741,a5621,a5622,a5623,a5624,s4_2747]) (PetersenIndexedNode.reasons 256 17 414 0x14040280a5001210114104a002501028209404084041405210118888422270102101200388404622240075888884042111210120037001a24040a02884444808490900c040602840441c0a0c052424838148092101006020301140500c040603001930a0884045014614114054006006020301211100c040603001730a09850484446141211140058060203014808141012000840448402400120209080480821010a08084041c0d242007014280a28200a02870345040140d0a0292100280a381824200e040422228201c080e06050403818108892100422209889410026020301383000c0426227060018880c04a080030146060a081180884046460210111818c8c0420621010504084041405400545004062414100a008501428201405018920028062480090a0805040422224201a082002648402420108885040282005849210016020301141000c0416122820018480c04908003014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406020312018080c04280a13110a0280c48262203100a0280c0406023a1a018080c044222626010888e868c4c0381a108880c0406020302212000c0003010301018000c080602030100c05090003012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060251110989144408404800821011444500115011210104c4884048007c00385414280a13120a0288444262421101c0c084c0422021111098084447030131209892001b000c212000c044c4803018005098904c4850401b1a0d89200163634131a141004c4826241511098905440282080040a0805445000914110a0804c4828201311109804c4006021312018084c44262413110180884c00602428280c080604840441c120c090a0a83824202a101006040302800300c080604280a10900840a000e212001900a02806040302800200c080604422230b018482000a616010b010888060403020180c000c06000604018100c00060203020180818120004060428a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b02252410920180806040302800000c0806042624119108c820002232210910989006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1618 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3004 theta)
    · exact b4_2353 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2031 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1490 theta)
    · exact b4_2745 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1806 theta)
    · exact b4_2744 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1448 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3002 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1190 theta)
    · exact b4_2749 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1203 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1202 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1117 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1114 theta)
    · exact b4_548 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_3007 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1648 theta)
    · exact b4_2746 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2363 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1929 theta)
    · exact b4_2740 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1113 theta)
    · exact b4_2741 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_96 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_762 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_761 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_786 theta)
    · exact b4_2747 theta
theorem b3_2964 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2964 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_2964 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w103 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2965 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2965 := by
  intro m le c
  apply rejects_sound extra111 i5 4 tgt small111 hot111 [] s3_2965 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons stored184 (PetersenWireProjection.cons pc111w113 (PetersenWireProjection.cons stored183 (PetersenWireProjection.cons stored182 (PetersenWireProjection.cons stored181 (PetersenWireProjection.cons stored180 (PetersenWireProjection.cons stored179 (PetersenWireProjection.cons stored178 (PetersenWireProjection.cons pc111w106 (PetersenWireProjection.cons stored177 rfl)))))))))) (by decide +kernel)
theorem b3_2966 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2966 := by
  apply PetersenIndexedNode.close (bank := [s4_2262,a5625,a5626,s4_2855,s4_2723,a4708,a4756,s4_2819,a5627,a5628,a5629,a5630,a5631,a5632,a5633,s4_2875,a5634,s4_1429,a5635,a5636,s4_2640,a5637,a5638,a5639,a5640,a5641,a5642,a5643,a5644,a5645,a5646,a5647,a5648,s4_2755,a5649,s4_2756,a5650,s4_2753]) (PetersenIndexedNode.reasons 256 17 432 0x80121888988088404644421012004ac888644421010c4448404511118505400084045040280014444a080511121010c2828404311128200c444c88830a098504c4446141211132221410042224808141012000840448402400120209080480821010a0808404381824200e040622228201c080e060504038181888921006222801114100a080614138301c10200467060283018504a080504046060a081180884046460210111818c8c04206210105040840464440a0805040622224201a08191104840242018888504028205444121009080614114100a08151102820141018504908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406023a1a018080c046222626018888e868c4c0381a188880c04060232a2818080c046141131109888ca8a26221311185040c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301311100c0406027030212018880c444424031111c0c006020301801000c04060261411312098920042262413121850406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c0406040301212000602030151114007944448404800ea10114445001f501021012003884043111400688404c888800c90808c445001b3111322220030c88830a0c00584202a080800a88404c283001730a0a82020028a080282040048a08090808008a4200a0810013282024202002090801410400385040c8c08006b23005041000f1410323020018c8c01311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c0600080301428280c080604840441c120c090a0a83824202a10100604030264c480c080604622230b0184819312616010b0188880604030230a080c080604a080109008480c28221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c08060500011090084820006212010904000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2262 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1200 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1672 theta)
    · exact b4_2855 theta
    · exact b4_2723 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_155 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_97 theta)
    · exact b4_2819 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2313 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1577 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1197 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2864 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2344 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1543 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1199 theta)
    · exact b4_2875 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2403 theta)
    · exact b4_1429 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1185 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2883 theta)
    · exact b4_2640 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_543 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_533 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2893 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2694 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_525 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_505 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2887 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2610 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1091 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1192 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2918 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_775 theta)
    · exact b4_2755 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1489 theta)
    · exact b4_2756 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_767 theta)
    · exact b4_2753 theta
theorem b3_2967 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2967 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2967 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w126 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w121 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_2968 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2968 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2968 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w129 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w128 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2969 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2969 := by
  apply PetersenIndexedNode.close (bank := [s4_2264,a5651,a5652,s4_2857,a4259,s4_725,s4_701,a5653,a5654,a5655,a5656,a5657,s4_3180,a5658,s4_2766,a5659,s4_1433,a5660,a5661,a5662,a5663,a5664,a5665,s4_2653,a5666,a5667,a5668,a5669,a5670,a5671,a5672,a5673,a5674,a5675,s4_2765]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108090808c282420231111850484444202108088404840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c04a0201080a80010808a0805000280814100a020420208404420270341080884048404614521011c0d0c28a4222210108404420226221080884040c0425051280898884a0a21050301084044202901028202400108089080480024041210090104202141010808501048401400084045040280014040a0805010210124200840416122820058080c045444030105848a88806120301141000c04311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a08084040e0a1410038080c042c240301038285848060a03010a0800c04280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a08050410020018080c050809000642024008a00429012210100c04840048082120108008404424021011202006020301030100c040c0084800302018000c04060403012120006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a0800602030180104007d242484048002210118505001d61411080a0038420261414007985044202800d908090d05001943410180a003006024341400690d040602800b818094505001551410840600282101514140059450421018009884052505001149411410200205040494140049250450408007941020017000a80048a082001028208007400360018282080038a082000d000541c080c0600080301428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030242c080c08060406021292018090b02252410920180806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030201808848006000604018100c000602030201808181042400604800100c080605000141c120e0a0006838241c14000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2264 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1284 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1433 theta)
    · exact b4_2857 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_8 theta)
    · exact b4_725 theta
    · exact b4_701 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2382 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1403 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1260 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1257 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1259 theta)
    · exact b4_3180 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_3111 theta)
    · exact b4_2766 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2264 theta)
    · exact b4_1433 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1284 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2857 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2604 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_523 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1273 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3112 theta)
    · exact b4_2653 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1228 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1291 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3113 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2604 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_523 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1273 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_3112 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_725 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_701 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2765 theta)
    · exact b4_2765 theta
theorem b3_2970 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2970 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2970 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w130 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2971 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2971 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2971 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2972 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2972 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_2972 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w141 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons pc73w134 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_2973 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2973 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2973 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w101 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2974 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2974 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_2974 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2975 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2975 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2975 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2976 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2976 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2976 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w38 rfl)))))))))) (by decide +kernel)
theorem b3_2977 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2977 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,true))] s3_2977 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w147 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w145 rfl)))))))))) (by decide +kernel)
theorem b3_2978 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2978 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2978 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w131 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w149 rfl)))))))))) (by decide +kernel)
theorem b3_2979 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2979 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,true))] s3_2979 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w151 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w150 rfl)))))))))) (by decide +kernel)
theorem b3_2980 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2980 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2980 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w153 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w40 rfl)))))))))) (by decide +kernel)
theorem b3_2981 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2981 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,true))] s3_2981 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w147 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w156 (PetersenWireProjection.cons pc26w155 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
