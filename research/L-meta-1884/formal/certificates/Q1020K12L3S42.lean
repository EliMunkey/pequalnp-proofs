import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S2
import Q1020K12L4S9
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S15
import Q1020K12L4S19
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S27
import Q1020K12L4S30
import Q1020K12L4S31
import Q1020K12L4S32
import Q1020K12L4S53
import Q1020K12L4S54
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S64
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S69
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc1w3 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc1w7 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl

private theorem pc1w11 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w12 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 stored59 stored63 rfl rfl
private theorem pc1w10 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w11 pc1w12 rfl rfl







private theorem pc3w19 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w23 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w24 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w22 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w23 pc3w24 rfl rfl
private theorem pc3w25 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl







private theorem pc26w31 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl

private theorem pc26w35 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f0000ffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w35 pc26w37 rfl rfl





private theorem pc32w43 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored27 stored28 rfl rfl



private theorem pc32w47 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w49 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored26 stored29 rfl rfl
private theorem pc32w46 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w47 pc32w49 rfl rfl
private theorem pc32w50 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored26 stored28 rfl rfl
private theorem pc32w52 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w50 stored24 rfl rfl
private theorem pc32w53 : PetersenPackedPin.project extra32 (0x3300330033003300330033003300330033003300330033003300330033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored28 stored29 rfl rfl
private theorem pc32w51 : PetersenPackedPin.project extra32 (0xff00ff0033003300ff00ff003300330033003300330033003300330033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w52 pc32w53 rfl rfl
private theorem pc32w54 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored25 stored28 rfl rfl
private theorem pc32w55 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w57 : PetersenPackedPin.project extra32 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w49 stored28 rfl rfl
private theorem pc32w56 : PetersenPackedPin.project extra32 (0xff00ff00ffccffccff00ff00ffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w57 pc32w47 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl






private theorem pc30w63 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl


private theorem pc30w68 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w70 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w67 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x55005500ff00ff0055005500ff00ff00 := PetersenWireProjection.derive 3 pc30w68 pc30w70 rfl rfl
private theorem pc32w71 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl



private theorem pc2w75 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored42 stored43 rfl rfl





private theorem pc2w81 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl
private theorem pc2w83 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w80 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w81 pc2w83 rfl rfl
private theorem pc1w84 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl
private theorem pc26w85 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc2w86 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w81 stored43 rfl rfl
private theorem pc3w89 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored34 stored35 rfl rfl
private theorem pc3w88 : PetersenPackedPin.project cycle3 (0xffffffff00000000000000000000000000000000000000000000000000000000 : BitVec 256) = 0xc0c00000 := PetersenWireProjection.derive 0 pc3w89 stored33 rfl rfl
private theorem pc3w90 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w87 : PetersenPackedPin.project cycle3 (0xffffffff33333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w88 pc3w90 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc2w92 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc32w94 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl




private theorem pc34w97 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl




private theorem pc34w104 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored18 stored22 rfl rfl
private theorem pc34w103 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w104 pc34w106 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w24 stored34 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000ccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w108 pc3w23 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc32w110 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc2w111 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
private theorem pc1w112 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl
private theorem pc1w113 : PetersenPackedPin.project cycle1 (0xffffffff00000000ccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 2 pc1w3 pc1w84 rfl rfl



private theorem pc73w115 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl





private theorem pc73w124 : PetersenPackedPin.project extra73 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x8888888888888888 := PetersenWireProjection.derive 0 stored129 stored131 rfl rfl
private theorem pc73w123 : PetersenPackedPin.project extra73 (0xffffffff00000000ccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w124 pc73w115 rfl rfl
private theorem pc34w125 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w127 : PetersenPackedPin.project extra34 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored17 stored20 rfl rfl
private theorem pc34w128 : PetersenPackedPin.project extra34 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored18 stored20 rfl rfl
private theorem pc34w126 : PetersenPackedPin.project extra34 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc34w127 pc34w128 rfl rfl
private theorem pc34w130 : PetersenPackedPin.project extra34 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored19 stored20 rfl rfl
private theorem pc34w129 : PetersenPackedPin.project extra34 (0xff000000ff000000ff00000000000000ff000000ff000000ff00000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 1 pc34w125 pc34w130 rfl rfl
private theorem pc34w131 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w133 : PetersenPackedPin.project extra34 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored18 stored23 rfl rfl
private theorem pc34w134 : PetersenPackedPin.project extra34 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored22 stored23 rfl rfl
private theorem pc34w132 : PetersenPackedPin.project extra34 (0x5555555544444444555555554444444455555555444444445555555544444444 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc34w133 pc34w134 rfl rfl
private theorem pc34w136 : PetersenPackedPin.project extra34 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored19 stored23 rfl rfl
private theorem pc34w135 : PetersenPackedPin.project extra34 (0x555500004444000055550000444400005555000044440000555500004444 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 1 pc34w131 pc34w136 rfl rfl
private theorem pc26w138 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w139 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w137 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xddddddddddddddddcccccccccccccccc := PetersenWireProjection.derive 2 pc26w138 pc26w139 rfl rfl
private theorem pc26w141 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w142 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w140 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa000000000000aaaa0000aaaa0000aaaa000000000000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w141 pc26w142 rfl rfl
private theorem pc26w144 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w143 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w144 pc26w138 rfl rfl
private theorem pc26w146 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w145 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w146 pc26w142 rfl rfl
private theorem pc26w147 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w149 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 1 stored1 stored4 rfl rfl
private theorem pc26w150 : PetersenPackedPin.project extra26 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0xffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored4 rfl rfl
private theorem pc26w148 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000 : BitVec 256) = 0xffffffff00000000aaaaaaaa := PetersenWireProjection.derive 3 pc26w149 pc26w150 rfl rfl
theorem b3_1764 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1764 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,false))] s3_1764 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xc0c0c0c0,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w10 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w7 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w3 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1765 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1765 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1765 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w19 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1766 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1766 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1766 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w25 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1767 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1767 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,false))] s3_1767 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1768 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1768 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1768 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w43 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1769 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1769 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1769 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w50 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1770 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1770 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1770 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w51 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1771 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1771 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1771 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w54 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1772 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1772 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1772 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1773 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1773 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1773 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w56 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1774 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1774 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,false))] s3_1774 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w58 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1775 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1775 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(0,false)),(false,(0,true),(4,false))] s3_1775 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x55005500ff00ff0055005500ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w67 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w63 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1776 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1776 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1776 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w71 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1777 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1777 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1777 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w80 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w75 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1778 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1778 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1778 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0xfcfcfcfc,0x0] (PetersenWireProjection.cons pc1w10 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w3 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w84 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1779 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1779 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,false))] s3_1779 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f00000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w85 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1780 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1780 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1780 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w80 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w86 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1781 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1781 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1781 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w87 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1782 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1782 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,false))] s3_1782 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1783 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1783 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1783 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w80 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w92 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1784 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1784 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(0,false)),(false,(0,true),(4,false))] s3_1784 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x55005500ff00ff0055005500ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w67 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w93 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1785 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1785 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1785 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w94 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1786 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1786 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1786 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w97 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1787 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1787 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1787 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w107 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1788 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1788 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,false))] s3_1788 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w109 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1789 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1789 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1789 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w25 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1790 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1790 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(1,false))] s3_1790 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w46 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w110 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_1791 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1791 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1791 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w80 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w111 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1792 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1792 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_1792 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0,0xffff0000] (PetersenWireProjection.cons pc1w10 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w112 rfl))))))))) (by decide +kernel)
theorem b3_1793 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1793 := by
  apply PetersenIndexedNode.close (bank := [s4_1311,a4800,a4801,s4_2544,a4802,a4664,a4803,s4_2812,a4804,a4805,a4806,a4807,a4808,a4809,a4810,a4811,a4812,s4_1298,a4813,a4814,a4528,a4815,a4816,s4_2898,a4817,a4756,a4818,a4819,a4820,a4821,a4822,a4823,s4_1351,a4824,a4825,a4826,s4_570,a4827,a4828,s4_1353,a4829,s4_1354,a4830,s4_1352]) (PetersenIndexedNode.reasons 256 17 432 0x8015108088404840461413080a0056c28221412101084044202501008405400084045040280014040a080501021010420221018014084044202420230a09080a0052614130a090808420221014808141012000840448402400120209080480821010a0808404290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840425050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406028013018080c04420262601080a004ec4c04260108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060249090989124248404801221011242500254909210104c4884042101098908404c888212010900840442402101322204c48480a8011109004602210113120840600462624131208404848021014941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080100a0805445002114110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c120c090a0a83824202a10100604030264c480c080604420230b0108099312616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c08868203020181098904240212049094007924248404800ea10112425001f490921012003884042101400688404c888800c920208405001b2101322220030c88830a0c0058c2822101800a88404c283001715050840600282101282040048a08090808008a4200a0810013282024202002090802420400389080282080068a0809081000f24200a082001828200301400280c0426228004898880c05000b03010988a0010262221204001806022624800280c048481000721200989200082624018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1311 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1298 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2307 theta)
    · exact b4_2544 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1334 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_97 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2606 theta)
    · exact b4_2812 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1313 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1299 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2260 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2553 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1313 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1299 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2260 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2553 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1311 theta)
    · exact b4_1298 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2307 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2544 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_505 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_836 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2694 theta)
    · exact b4_2898 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1334 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_97 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2606 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2812 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_505 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_836 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2694 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2898 theta)
    · exact b4_1351 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1353 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_668 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1352 theta)
    · exact b4_570 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1354 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1351 theta)
    · exact b4_1353 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_570 theta)
    · exact b4_1354 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_668 theta)
    · exact b4_1352 theta
theorem b3_1794 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1794 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1794 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w113 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w3 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1795 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1795 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_1795 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w123 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons pc73w115 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_1796 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1796 := by
  apply PetersenIndexedNode.close (bank := [s4_1315,a4831,a4832,s4_2559,s4_1345,s4_1338,s4_1337,a4833,a4834,a4835,s4_2836,a4836,a4837,a4838,a4839,a4840,a4841,a4842,a4843,a4844,s4_1300,a4845,a4846,s4_902,a4847,a4545,s4_2918,a4848,a4849,a4850,a4851,a4852,a4793,a4853,a4854,s4_1155,a4855,a4676,a4856,s4_1361,a4857,a4858,s4_1358,a4859,a4860,s4_1359,a4861,a4862,a4863,a4864]) (PetersenIndexedNode.reasons 256 17 432 0x622210808840484046141308098888c28262222101084044202501008405400084045040280014040a080501021010420221013111084044202420230a090808c4446141211110808420221014808141012000840448402400120209080480821010a0808404290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840425050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406028018018080c04420262601080a0062c4c06260108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490910901242484046160210112424c2c0490921010848084042101400bc8405002e212010900840442402101400b60058480a150510900541421013130084045414626015050840484802101494110900848050408015141012505002b494114100848042401511109005444282080140a0805445002915110a080848028200301109000c0484802322119000c04464403012120084804240428280c080604840441c120c090a0a83824202a101006040302801300c080604420230b01080a004e616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c088682030201811090042402120490940091242484048011a101124250025490921012004484042101400808405001f800f12020840500212101400760039001b15054006454142101800c084045415001a150508406002e2101282040054a0809080800a24200a0810016282024202002690801511400445444282080080a0805445001215110a082001e28200301400340c0484808006212000c05000e0301212020016848021204002406030008800380c048481000a21204001a000b0004018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1315 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1300 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2258 theta)
    · exact b4_2559 theta
    · exact b4_1345 theta
    · exact b4_1338 theta
    · exact b4_1337 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_403 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_400 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2599 theta)
    · exact b4_2836 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1315 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1300 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2258 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2559 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1315 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1300 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2258 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2559 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1315 theta)
    · exact b4_1300 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2258 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2559 theta)
    · exact b4_902 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1155 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2692 theta)
    · exact b4_2918 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1345 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1338 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1337 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_403 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_400 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2599 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2836 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_902 theta)
    · exact b4_1155 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2692 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2918 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1358 theta)
    · exact b4_1361 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1358 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1361 theta)
    · exact b4_1358 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1361 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1359 theta)
    · exact b4_1359 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_950 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_950 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1358 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1361 theta)
theorem b3_1797 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1797 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s3_1797 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xff00f000ff00f000ff00f000ff00f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w129 (PetersenWireProjection.cons pc34w126 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w125 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1798 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1798 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s3_1798 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xff00f000ff00f000ff00f000ff00f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w129 (PetersenWireProjection.cons pc34w126 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1799 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1799 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1799 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x32323232323232323232323232323232,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w135 (PetersenWireProjection.cons pc34w132 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w131 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1800 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1800 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1800 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x32323232323232323232323232323232,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w135 (PetersenWireProjection.cons pc34w132 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1801 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1801 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(2,true))] s3_1801 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xddddddddddddddddcccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w140 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w137 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1802 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1802 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1802 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w145 (PetersenWireProjection.cons pc26w143 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1803 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1803 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_1803 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w145 (PetersenWireProjection.cons pc26w143 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w146 rfl)))))))))) (by decide +kernel)
theorem b3_1804 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1804 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(6,true),(0,true))] s3_1804 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000aaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w142 (PetersenWireProjection.cons pc26w148 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w147 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1805 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1805 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(6,true),(0,true))] s3_1805 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000aaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w142 (PetersenWireProjection.cons pc26w148 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
