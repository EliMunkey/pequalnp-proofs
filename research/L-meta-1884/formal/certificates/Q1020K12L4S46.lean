import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0






private theorem pc74w7 : PetersenPackedPin.project extra74 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored114 stored119 rfl rfl
private theorem pc74w9 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc74w6 : PetersenPackedPin.project extra74 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc74w7 pc74w9 rfl rfl
private theorem pc74w10 : PetersenPackedPin.project extra74 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored119 rfl rfl
private theorem pc74w5 : PetersenPackedPin.project extra74 (0xccccccccccccccccccccccccccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w6 pc74w10 rfl rfl


private theorem pc74w13 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored116 rfl rfl
private theorem pc74w15 : PetersenPackedPin.project extra74 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored114 stored116 rfl rfl
private theorem pc74w12 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc74w13 pc74w15 rfl rfl
private theorem pc74w16 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl
private theorem pc74w18 : PetersenPackedPin.project extra74 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 2 stored113 stored114 rfl rfl
private theorem pc74w19 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored113 stored119 rfl rfl
private theorem pc74w17 : PetersenPackedPin.project extra74 (0xccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 3 pc74w18 pc74w19 rfl rfl






private theorem pc397w27 : PetersenPackedPin.project extra397 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored242 stored246 rfl rfl
private theorem pc397w26 : PetersenPackedPin.project extra397 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc397w27 stored241 rfl rfl
private theorem pc397w30 : PetersenPackedPin.project extra397 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored243 stored246 rfl rfl

private theorem pc397w31 : PetersenPackedPin.project extra397 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored247 stored246 rfl rfl
private theorem pc397w29 : PetersenPackedPin.project extra397 (0x3333333333330000333333333333000033333333333300003333333333330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc397w30 pc397w31 rfl rfl
private theorem pc397w25 : PetersenPackedPin.project extra397 (0xccccccccccccffffccccccccccccffffccccccccccccffffcccccccccccccccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 pc397w26 pc397w29 rfl rfl

private theorem pc397w35 : PetersenPackedPin.project extra397 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored241 stored247 rfl rfl
private theorem pc397w36 : PetersenPackedPin.project extra397 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored242 stored247 rfl rfl
private theorem pc397w34 : PetersenPackedPin.project extra397 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc397w35 pc397w36 rfl rfl






private theorem pc0w43 : PetersenPackedPin.project cycle0 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored51 stored55 rfl rfl
private theorem pc0w42 : PetersenPackedPin.project cycle0 (0xccccccccffffffff0000000000000000ccccccccffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w43 stored50 rfl rfl


private theorem pc0w47 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w49 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w46 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w47 pc0w49 rfl rfl






private theorem pc1w56 : PetersenPackedPin.project cycle1 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored59 stored63 rfl rfl
private theorem pc1w55 : PetersenPackedPin.project cycle1 (0xccccccccffffffffccccccccffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc1w56 stored57 rfl rfl


private theorem pc1w60 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w62 : PetersenPackedPin.project cycle1 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored58 stored60 rfl rfl
private theorem pc1w59 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w60 pc1w62 rfl rfl






private theorem pc116w70 : PetersenPackedPin.project extra116 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored106 stored111 rfl rfl
private theorem pc116w69 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc116w70 stored105 rfl rfl
private theorem pc116w72 : PetersenPackedPin.project extra116 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored107 stored111 rfl rfl
private theorem pc116w68 : PetersenPackedPin.project extra116 (0xccccccccffffffffccccccccffffffffccccccccffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc116w69 pc116w72 rfl rfl


private theorem pc116w75 : PetersenPackedPin.project extra116 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored105 stored108 rfl rfl
private theorem pc116w77 : PetersenPackedPin.project extra116 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored106 stored108 rfl rfl
private theorem pc116w74 : PetersenPackedPin.project extra116 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc116w75 pc116w77 rfl rfl






private theorem pc107w85 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored161 stored167 rfl rfl
private theorem pc107w87 : PetersenPackedPin.project extra107 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored162 stored167 rfl rfl
private theorem pc107w84 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w85 pc107w87 rfl rfl

private theorem pc107w88 : PetersenPackedPin.project extra107 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000 := PetersenWireProjection.derive 0 stored163 stored166 rfl rfl
private theorem pc107w83 : PetersenPackedPin.project extra107 (0xccccffff0000ffffccccffff0000ffffccccffff0000ffffcccccccc00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w84 pc107w88 rfl rfl








private theorem pc34w97 : PetersenPackedPin.project extra34 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored19 stored22 rfl rfl
private theorem pc34w96 : PetersenPackedPin.project extra34 (0xccccffffccccffff0000000000000000ccccffffccccffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 2 pc34w97 stored17 rfl rfl

private theorem pc34w102 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w103 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w101 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w102 pc34w103 rfl rfl
private theorem pc34w104 : PetersenPackedPin.project extra34 (0xccccffffccccffffccccffffccccffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 2 pc34w97 stored16 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w105 : PetersenPackedPin.project extra34 (0xccccffffccccffffccccffffccccffffccccffffccccffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 1 pc34w106 pc34w97 rfl rfl
private theorem pc107w109 : PetersenPackedPin.project extra107 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored166 rfl rfl
private theorem pc107w108 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w109 stored161 rfl rfl
private theorem pc107w110 : PetersenPackedPin.project extra107 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored167 stored166 rfl rfl
private theorem pc107w107 : PetersenPackedPin.project extra107 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w108 pc107w110 rfl rfl





private theorem pc26w118 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl


private theorem pc26w119 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl
private theorem pc26w117 : PetersenPackedPin.project extra26 (0x555500005555000055550000555500005555000055550000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 1 pc26w118 pc26w119 rfl rfl

private theorem pc26w122 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w116 : PetersenPackedPin.project extra26 (0xeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0xcdcd0000cdcd0000cdcd0000cdcd0000 := PetersenWireProjection.derive 2 pc26w117 pc26w122 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w125 pc26w126 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc26w128 pc26w122 rfl rfl
private theorem pc26w131 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w130 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w131 stored0 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafa0000fafa0000fafa0000fafa0000 := PetersenWireProjection.derive 0 pc26w130 pc26w122 rfl rfl
private theorem pc26w132 : PetersenPackedPin.project extra26 (0xeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffff3232ffff3232ffff3232ffff3232 := PetersenWireProjection.derive 3 pc26w124 pc26w122 rfl rfl





private theorem pc30w138 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored12 stored13 rfl rfl



private theorem pc30w142 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w144 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w141 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w142 pc30w144 rfl rfl
private theorem pc30w147 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w146 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w147 stored8 rfl rfl
private theorem pc30w148 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w145 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w146 pc30w148 rfl rfl
private theorem pc30w151 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w152 : PetersenPackedPin.project extra30 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored10 stored11 rfl rfl
private theorem pc30w150 : PetersenPackedPin.project extra30 (0xffff000000000000ffff000000000000ffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaa0a0a0a0 := PetersenWireProjection.derive 0 pc30w151 pc30w152 rfl rfl
private theorem pc30w149 : PetersenPackedPin.project extra30 (0xf0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w150 stored13 rfl rfl
private theorem pc30w155 : PetersenPackedPin.project extra30 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00 := PetersenWireProjection.derive 2 stored11 stored14 rfl rfl
private theorem pc30w154 : PetersenPackedPin.project extra30 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000000000000 : BitVec 256) = 0xff00ff00f000f000 := PetersenWireProjection.derive 0 pc30w151 pc30w155 rfl rfl
private theorem pc30w153 : PetersenPackedPin.project extra30 (0xf0f03030f0f03030f0f03030f0f03030f0f03030f0f03030f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w154 stored13 rfl rfl
private theorem pc30w158 : PetersenPackedPin.project extra30 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored11 stored14 rfl rfl
private theorem pc30w157 : PetersenPackedPin.project extra30 (0x333300003333000033330000333300003333000033330000000000000000 : BitVec 256) = 0xff00ff00f000f0 := PetersenWireProjection.derive 1 pc30w151 pc30w158 rfl rfl
private theorem pc30w156 : PetersenPackedPin.project extra30 (0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w157 stored13 rfl rfl
private theorem pc30w160 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w159 : PetersenPackedPin.project extra30 (0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w160 stored13 rfl rfl
private theorem pc30w163 : PetersenPackedPin.project extra30 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored11 rfl rfl
private theorem pc30w162 : PetersenPackedPin.project extra30 (0xffff000000000000ffff000000000000ffff0000000000000000 : BitVec 256) = 0x5555555550505050 := PetersenWireProjection.derive 1 pc30w151 pc30w163 rfl rfl
private theorem pc30w161 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w162 stored13 rfl rfl
private theorem pc30w164 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl
private theorem pc30w166 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored10 stored13 rfl rfl
private theorem pc30w165 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w164 pc30w166 rfl rfl
private theorem pc30w168 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w167 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f03030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w168 stored13 rfl rfl
private theorem pc30w170 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w169 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w170 stored13 rfl rfl
private theorem pc30w172 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w171 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w164 pc30w172 rfl rfl
private theorem pc30w173 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w174 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w173 pc30w166 rfl rfl
private theorem pc30w176 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w175 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w176 stored13 rfl rfl
private theorem pc30w178 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w177 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w178 stored13 rfl rfl
private theorem pc30w179 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w173 pc30w172 rfl rfl
private theorem pc30w180 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w165 pc30w173 rfl rfl
private theorem pc30w181 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w167 pc30w173 rfl rfl
theorem b4_1932 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1932 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_1932 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc74w12 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w5 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_1933 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1933 := by
  apply node_sound (nxt := [s5_30,a6609])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_30 theta
    · exact via sym6 fix6 (by decide +kernel) (b5_27 theta)
theorem b4_1934 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1934 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_1934 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc74w12 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w17 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w16 rfl))))))))) (by decide +kernel)
theorem b4_1935 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1935 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_1935 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc74w12 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w6 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_1936 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1936 := by
  intro m le c
  apply rejects_sound extra397 i5 4 tgt small397 hot397 [] s4_1936 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaa,0xcccccccc,0xffffffff,0xffff0000,0xff00ff00,0x0,0xf0f0f0f0,0xffffffff] (PetersenWireProjection.cons pc397w34 (PetersenWireProjection.cons stored248 (PetersenWireProjection.cons stored246 (PetersenWireProjection.cons pc397w25 (PetersenWireProjection.cons stored245 (PetersenWireProjection.cons stored244 (PetersenWireProjection.cons stored243 (PetersenWireProjection.cons stored242 (PetersenWireProjection.cons stored241 rfl))))))))) (by decide +kernel)
theorem b4_1937 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1937 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1937 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0x0,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w46 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w42 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_1938 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1938 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_1938 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w59 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w55 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_1939 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1939 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_1939 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffffffffffffffff,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w74 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons pc116w68 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl))))))))) (by decide +kernel)
theorem b4_1940 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1940 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_1940 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xffffffffffffffff,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w84 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons pc107w83 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_1941 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1941 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_1942 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1942 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1942 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w101 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w96 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1943 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1943 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1943 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w101 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1944 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1944 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1944 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w101 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w105 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1945 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1945 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_1945 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xffffffffffffffff,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w84 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons pc107w107 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_1946 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1946 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(0,true),(6,false))] s4_1946 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xcdcd0000cdcd0000cdcd0000cdcd0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w116 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1947 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1947 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,false),(8,false))] s4_1947 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff00000000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1948 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1948 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,false),(1,true))] s4_1948 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xfafa0000fafa0000fafa0000fafa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1949 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1949 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1949 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w122 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1950 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1950 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(0,true),(6,true))] s4_1950 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff3232ffff3232ffff3232ffff3232,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w132 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1951 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1951 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_1951 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w138 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1952 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1952 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_1952 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w145 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1953 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1953 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1953 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1954 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1954 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1954 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_1955 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1955 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1955 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w153 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1956 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1956 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1956 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w156 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1957 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1957 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1957 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w159 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1958 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1958 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1958 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w161 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1959 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1959 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_1959 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w164 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1960 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1960 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1960 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w165 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1961 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1961 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1961 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w167 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1962 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1962 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1962 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w169 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1963 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1963 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1963 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w171 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1964 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1964 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_1964 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w173 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1965 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1965 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1965 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w174 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1966 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1966 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1966 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w175 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1967 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1967 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1967 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w177 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1968 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1968 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1968 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w177 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_1969 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1969 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true)),(false,(5,true),(7,true))] s4_1969 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w177 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w178 rfl))))))))) (by decide +kernel)
theorem b4_1970 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1970 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true)),(false,(5,true),(7,true))] s4_1970 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w177 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w178 (PetersenWireProjection.cons pc30w151 rfl))))))))) (by decide +kernel)
theorem b4_1971 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1971 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1971 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w179 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1972 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1972 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(7,true),(0,true))] s4_1972 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w180 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1973 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1973 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1973 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w141 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w181 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
