import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc30w5 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored9 stored13 rfl rfl


private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl

private theorem pc30w9 : PetersenPackedPin.project extra30 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfff0fff0fff0fff0 := PetersenWireProjection.derive 1 pc30w10 stored11 rfl rfl
private theorem pc30w12 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w8 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w9 pc30w12 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w10 stored13 rfl rfl
private theorem pc30w14 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w16 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w15 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w16 stored13 rfl rfl
private theorem pc30w17 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w14 pc30w5 rfl rfl
private theorem pc30w18 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w13 pc30w14 rfl rfl
private theorem pc30w19 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w10 stored8 rfl rfl
private theorem pc30w22 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w21 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w16 pc30w22 rfl rfl
private theorem pc30w23 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored11 stored13 rfl rfl
private theorem pc30w20 : PetersenPackedPin.project extra30 (0xf0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fcfcf0f0fcfc : BitVec 256) = 0xfffffffffff0fff0 := PetersenWireProjection.derive 1 pc30w21 pc30w23 rfl rfl






private theorem pc26w28 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl

private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl

private theorem pc26w33 : PetersenPackedPin.project extra26 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0x33332222333322223333222233332222 := PetersenWireProjection.derive 1 pc26w34 stored3 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0x33333232333332323333323233333232 := PetersenWireProjection.derive 3 pc26w33 pc26w36 rfl rfl
private theorem pc30w37 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl





private theorem pc32w44 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored24 stored29 rfl rfl
private theorem pc32w46 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored25 stored28 rfl rfl
private theorem pc32w43 : PetersenPackedPin.project extra32 (0x3300330033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc32w44 pc32w46 rfl rfl

private theorem pc32w47 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored27 stored28 rfl rfl
private theorem pc32w42 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff003300ff003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w43 pc32w47 rfl rfl


private theorem pc32w53 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w52 : PetersenPackedPin.project extra32 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00aa00ff00aa00ff00aa00ff00aa := PetersenWireProjection.derive 1 pc32w53 stored27 rfl rfl
private theorem pc32w54 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w51 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00fa00ff00fa00ff00fa00ff00fa := PetersenWireProjection.derive 3 pc32w52 pc32w54 rfl rfl
private theorem pc32w55 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored26 stored28 rfl rfl
private theorem pc32w56 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored25 stored28 rfl rfl
private theorem pc32w57 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w53 stored28 rfl rfl
private theorem pc32w58 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w59 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w44 stored28 rfl rfl
private theorem pc32w60 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w58 pc32w56 rfl rfl
private theorem pc32w61 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w57 pc32w58 rfl rfl
private theorem pc32w64 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc32w63 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffffffccffccffccffcc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc32w44 pc32w64 rfl rfl
private theorem pc32w65 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 1 stored27 stored28 rfl rfl
private theorem pc32w62 : PetersenPackedPin.project extra32 (0xff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffccff00ffcc : BitVec 256) = 0xff00fa00ff00fa00ff00fa00ff00fa := PetersenWireProjection.derive 1 pc32w63 pc32w65 rfl rfl
private theorem pc26w66 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl
private theorem pc32w67 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc30w68 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl




private theorem pc107w74 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored161 stored166 rfl rfl

private theorem pc107w73 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc107w74 stored167 rfl rfl
private theorem pc107w78 : PetersenPackedPin.project extra107 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored162 stored167 rfl rfl
private theorem pc107w77 : PetersenPackedPin.project extra107 (0xffff000000000000ffffffff00000000ffff000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc107w78 stored163 rfl rfl
private theorem pc107w72 : PetersenPackedPin.project extra107 (0xffff000000000000ffff000000000000ffff000000000000ffff333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc107w73 pc107w77 rfl rfl



private theorem pc107w84 : PetersenPackedPin.project extra107 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored166 rfl rfl
private theorem pc107w83 : PetersenPackedPin.project extra107 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w84 stored167 rfl rfl
private theorem pc107w85 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored161 stored167 rfl rfl
private theorem pc107w82 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w83 pc107w85 rfl rfl




private theorem pc34w89 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored17 stored19 rfl rfl




private theorem pc34w97 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w96 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w97 stored19 rfl rfl
private theorem pc34w98 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w95 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w96 pc34w98 rfl rfl
private theorem pc34w99 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w97 stored19 rfl rfl
private theorem pc34w100 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored16 stored19 rfl rfl
private theorem pc34w102 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w101 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w102 stored19 rfl rfl
private theorem pc34w103 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w100 pc34w89 rfl rfl
private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w99 pc34w100 rfl rfl



private theorem pc0w108 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl




private theorem pc0w115 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w114 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc0w115 stored52 rfl rfl
private theorem pc0w117 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w113 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 pc0w114 pc0w117 rfl rfl




private theorem pc116w122 : PetersenPackedPin.project extra116 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored106 stored111 rfl rfl
private theorem pc116w121 : PetersenPackedPin.project extra116 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc116w122 stored107 rfl rfl




private theorem pc116w128 : PetersenPackedPin.project extra116 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 1 pc116w122 stored108 rfl rfl
private theorem pc116w130 : PetersenPackedPin.project extra116 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored105 stored108 rfl rfl
private theorem pc116w127 : PetersenPackedPin.project extra116 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc116w128 pc116w130 rfl rfl



private theorem pc1w134 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc1w141 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl

private theorem pc1w140 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 1 pc1w141 stored60 rfl rfl
private theorem pc1w143 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w139 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc1w140 pc1w143 rfl rfl
private theorem pc116w145 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored111 rfl rfl
private theorem pc116w144 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc116w145 stored107 rfl rfl
private theorem pc116w147 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored105 stored107 rfl rfl
private theorem pc116w148 : PetersenPackedPin.project extra116 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored106 stored107 rfl rfl
private theorem pc116w146 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc116w147 pc116w148 rfl rfl
private theorem pc116w149 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc116w121 pc116w147 rfl rfl
private theorem pc107w152 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored163 rfl rfl
private theorem pc107w151 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w74 pc107w152 rfl rfl
private theorem pc107w153 : PetersenPackedPin.project extra107 (0xffff000000000000ffff000000000000ffff000000000000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored163 stored167 rfl rfl
private theorem pc107w150 : PetersenPackedPin.project extra107 (0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w151 pc107w153 rfl rfl
private theorem pc26w154 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl




private theorem pc29w157 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl



private theorem pc29w165 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl

private theorem pc29w164 : PetersenPackedPin.project extra29 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 1 pc29w165 stored157 rfl rfl
private theorem pc29w167 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored153 stored157 rfl rfl
private theorem pc29w163 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 3 pc29w164 pc29w167 rfl rfl
theorem b4_2142 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2142 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2142 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w5 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2143 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2143 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true)),(false,(6,true),(0,false)),(false,(8,true),(0,true))] s4_2143 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2144 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2144 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2144 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2145 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2145 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,false),(3,true)),(false,(8,true),(0,true))] s4_2145 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2146 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2146 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,false),(3,true)),(false,(8,true),(0,true))] s4_2146 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w15 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_2147 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2147 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,false),(3,true)),(false,(8,true),(0,true))] s4_2147 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w15 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w16 rfl))))))))) (by decide +kernel)
theorem b4_2148 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2148 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2148 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w17 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2149 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2149 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2149 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2150 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2150 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2150 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_2151 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2151 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2151 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffffff0fff0fffffffffff0fff0] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w19 rfl))))))))) (by decide +kernel)
theorem b4_2152 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2152 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2152 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfffffffffff0fff0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w20 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2153 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2153 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2153 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2154 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2154 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2154 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2155 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2155 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2155 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w42 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2156 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2156 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2156 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2157 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2157 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2157 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w56 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2158 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2158 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,false)),(false,(5,true),(0,true))] s4_2158 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w57 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2159 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2159 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2159 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w58 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2160 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2160 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(5,true),(0,true))] s4_2160 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w59 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2161 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2161 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2161 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w60 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2162 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2162 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2162 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w61 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2163 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2163 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2163 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w62 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2164 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2164 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2164 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w66 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2165 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2165 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2165 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2166 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2166 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2166 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w8 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2167 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2167 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_2167 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w82 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons pc107w72 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_2168 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2168 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2168 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w89 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2169 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2169 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,false))] s4_2169 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w99 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2170 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2170 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2170 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w100 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2171 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2171 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true)),(false,(0,false),(5,true))] s4_2171 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w101 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2172 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2172 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2172 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2173 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2173 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2173 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2174 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2174 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true)),(false,(0,false),(5,false)),(false,(0,true),(1,false))] s4_2174 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w95 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2175 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2175 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s4_2175 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffccffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w113 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w108 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2176 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2176 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_2176 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w127 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons pc116w121 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl))))))))) (by decide +kernel)
theorem b4_2177 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2177 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s4_2177 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w139 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w134 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2178 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2178 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_2178 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w127 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons pc116w144 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl))))))))) (by decide +kernel)
theorem b4_2179 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2179 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_2179 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w127 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons pc116w146 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl))))))))) (by decide +kernel)
theorem b4_2180 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2180 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_2180 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w127 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons pc116w149 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl))))))))) (by decide +kernel)
theorem b4_2181 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2181 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_2181 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w82 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons pc107w150 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_2182 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2182 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2182 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w154 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2183 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2183 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2183 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc29w163 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w157 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
