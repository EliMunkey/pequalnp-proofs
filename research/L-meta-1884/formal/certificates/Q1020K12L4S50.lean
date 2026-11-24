import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc34w6 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl

private theorem pc34w5 : PetersenPackedPin.project extra34 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc34w6 stored20 rfl rfl
private theorem pc34w9 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w4 : PetersenPackedPin.project extra34 (0xffccffccffccffccffccffccffccffccffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffaaffaaffaaffaaffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc34w5 pc34w9 rfl rfl


private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w13 pc34w14 rfl rfl


private theorem pc74w15 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl


private theorem pc74w21 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl

private theorem pc74w20 : PetersenPackedPin.project extra74 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc74w21 stored117 rfl rfl
private theorem pc74w24 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored113 stored119 rfl rfl
private theorem pc74w19 : PetersenPackedPin.project extra74 (0xffccffccffccffccffccffccffccffccffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc74w20 pc74w24 rfl rfl



private theorem pc74w28 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored116 rfl rfl
private theorem pc74w30 : PetersenPackedPin.project extra74 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored114 stored116 rfl rfl
private theorem pc74w27 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc74w28 pc74w30 rfl rfl
private theorem pc34w33 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w32 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc34w33 stored18 rfl rfl
private theorem pc34w31 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000cccc : BitVec 256) = 0xffffffffffffffffffff0a0affff0a0a := PetersenWireProjection.derive 3 pc34w12 pc34w32 rfl rfl


private theorem pc39w35 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl


private theorem pc39w38 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x33330000333300003333000033330000 := PetersenWireProjection.derive 2 stored75 stored79 rfl rfl
private theorem pc39w34 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff00000000cccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w35 pc39w38 rfl rfl




private theorem pc39w46 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w48 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored74 stored76 rfl rfl
private theorem pc39w45 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w46 pc39w48 rfl rfl
private theorem pc39w50 : PetersenPackedPin.project extra39 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored76 stored79 rfl rfl
private theorem pc39w49 : PetersenPackedPin.project extra39 (0xcccc000000000000cccc000000000000cccc000000000000cccc : BitVec 256) = 0x3333000033330000 := PetersenWireProjection.derive 1 pc39w50 stored75 rfl rfl
private theorem pc39w44 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff000000000000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w45 pc39w49 rfl rfl
private theorem pc34w52 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc34w33 stored18 rfl rfl
private theorem pc34w51 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc00000000 : BitVec 256) = 0xffffffffffffffffffffa0a0ffffa0a0 := PetersenWireProjection.derive 3 pc34w12 pc34w52 rfl rfl
private theorem pc39w54 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc0000 := PetersenWireProjection.derive 0 stored75 stored79 rfl rfl
private theorem pc39w53 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w35 pc39w54 rfl rfl
private theorem pc39w56 : PetersenPackedPin.project extra39 (0xcccc000000000000cccc000000000000cccc000000000000cccc00000000 : BitVec 256) = 0xcccc0000cccc0000 := PetersenWireProjection.derive 0 pc39w50 stored75 rfl rfl
private theorem pc39w55 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w45 pc39w56 rfl rfl







private theorem pc30w66 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w65 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 1 pc30w66 stored13 rfl rfl
private theorem pc30w67 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w64 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w65 pc30w67 rfl rfl

private theorem pc30w69 : PetersenPackedPin.project extra30 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfff0fff0fff0fff0 := PetersenWireProjection.derive 1 pc30w66 stored11 rfl rfl
private theorem pc30w71 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w68 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w69 pc30w71 rfl rfl


private theorem pc29w73 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl

private theorem pc29w72 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w73 stored153 rfl rfl




private theorem pc29w81 : PetersenPackedPin.project extra29 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 1 pc29w73 stored159 rfl rfl
private theorem pc29w83 : PetersenPackedPin.project extra29 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 1 stored153 stored159 rfl rfl
private theorem pc29w80 : PetersenPackedPin.project extra29 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 3 pc29w81 pc29w83 rfl rfl

private theorem pc29w85 : PetersenPackedPin.project extra29 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 1 pc29w73 stored157 rfl rfl
private theorem pc29w87 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored153 stored157 rfl rfl
private theorem pc29w84 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 3 pc29w85 pc29w87 rfl rfl







private theorem pc26w95 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w98 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl

private theorem pc26w97 : PetersenPackedPin.project extra26 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0x33332222333322223333222233332222 := PetersenWireProjection.derive 1 pc26w98 stored3 rfl rfl
private theorem pc26w100 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w96 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0x33333232333332323333323233333232 := PetersenWireProjection.derive 3 pc26w97 pc26w100 rfl rfl
private theorem pc26w101 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl
private theorem pc26w102 : PetersenPackedPin.project extra26 (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored4 stored7 rfl rfl
private theorem pc26w105 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w104 : PetersenPackedPin.project extra26 (0x2222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w105 pc26w98 rfl rfl
private theorem pc26w106 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored3 stored7 rfl rfl
private theorem pc26w103 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa2222aaaa2222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w104 pc26w106 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w108 pc26w95 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa88888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w110 pc26w95 rfl rfl
private theorem pc26w112 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w110 pc26w108 rfl rfl
private theorem pc26w113 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w109 pc26w110 rfl rfl
private theorem pc26w116 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w116 pc26w98 rfl rfl
private theorem pc26w117 : PetersenPackedPin.project extra26 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 1 stored3 stored7 rfl rfl
private theorem pc26w114 : PetersenPackedPin.project extra26 (0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaeeeeaaaaeeee : BitVec 256) = 0x33333232333332323333323233333232 := PetersenWireProjection.derive 1 pc26w115 pc26w117 rfl rfl
private theorem pc30w118 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl






private theorem pc32w125 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl

private theorem pc32w129 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl

private theorem pc32w128 : PetersenPackedPin.project extra32 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00aa00ff00aa00ff00aa00ff00aa := PetersenWireProjection.derive 1 pc32w129 stored27 rfl rfl
private theorem pc32w131 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w127 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00fa00ff00fa00ff00fa00ff00fa := PetersenWireProjection.derive 3 pc32w128 pc32w131 rfl rfl
private theorem pc34w132 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl
private theorem pc34w135 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w134 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w135 stored19 rfl rfl
private theorem pc34w133 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w134 pc34w13 rfl rfl






private theorem pc3w142 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w146 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl

private theorem pc3w145 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 pc3w146 stored36 rfl rfl
private theorem pc3w148 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored33 stored36 rfl rfl
private theorem pc3w144 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00f0 := PetersenWireProjection.derive 3 pc3w145 pc3w148 rfl rfl






private theorem pc0w155 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w159 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w158 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc0w159 stored52 rfl rfl
private theorem pc0w161 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w157 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 pc0w158 pc0w161 rfl rfl
private theorem pc3w162 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl






private theorem pc1w169 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl

private theorem pc1w173 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl

private theorem pc1w172 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 1 pc1w173 stored60 rfl rfl
private theorem pc1w175 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w171 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc1w172 pc1w175 rfl rfl
private theorem pc3w176 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w177 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc1w178 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc3w179 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w177 pc3w162 rfl rfl
private theorem pc39w181 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl
private theorem pc39w180 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w181 stored73 rfl rfl
private theorem pc39w183 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored73 stored79 rfl rfl
private theorem pc39w184 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 0 stored74 stored79 rfl rfl
private theorem pc39w182 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 pc39w183 pc39w184 rfl rfl
private theorem pc39w186 : PetersenPackedPin.project extra39 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc39w181 stored76 rfl rfl
private theorem pc39w185 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w186 pc39w46 rfl rfl
private theorem pc34w188 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w135 stored16 rfl rfl
private theorem pc34w189 : PetersenPackedPin.project extra34 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored19 stored22 rfl rfl
private theorem pc34w187 : PetersenPackedPin.project extra34 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w188 pc34w189 rfl rfl
private theorem pc26w190 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc30w191 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored12 stored13 rfl rfl
private theorem pc30w194 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w195 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w193 : PetersenPackedPin.project extra30 (0x3030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w194 pc30w195 rfl rfl
private theorem pc30w196 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w192 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f03030f0f03030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w193 pc30w196 rfl rfl
private theorem pc30w197 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
theorem b4_2100 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2100 := by
  apply node_sound (nxt := [a6610,a6611])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_8 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_32 theta)
theorem b4_2101 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2101 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,true),(1,false)),(false,(0,true),(5,true))] s4_2101 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xffaaffaaffaaffaaffaaff00ffaaff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons pc34w4 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2102 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2102 := by
  apply node_sound (nxt := [a6612,a6613])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_9 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_33 theta)
theorem b4_2103 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2103 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2103 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc74w27 (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons pc74w19 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w15 rfl))))))))) (by decide +kernel)
theorem b4_2104 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2104 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(7,true),(5,true)),(false,(1,true),(0,false))] s4_2104 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0a0affff0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w31 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2105 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2105 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2106 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2106 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2106 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w44 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w34 rfl))))))))) (by decide +kernel)
theorem b4_2107 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2107 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(5,true),(7,true)),(false,(1,true),(0,false))] s4_2107 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffa0a0ffffa0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2108 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2108 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2109 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2109 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2109 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w55 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w53 rfl))))))))) (by decide +kernel)
theorem b4_2110 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2110 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2110 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xfffffffffff0fff0fffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons pc30w64 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2111 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2111 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2112 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2112 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2112 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00ff00ff00ff00ff,0xffffffff00000000ffffffff,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w84 (PetersenWireProjection.cons pc29w80 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w72 rfl))))))))) (by decide +kernel)
theorem b4_2113 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2113 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2113 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w95 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2114 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2114 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2114 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w101 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2115 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2115 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2115 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w102 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2116 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2116 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2116 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w103 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2117 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2117 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2117 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w107 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2118 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2118 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2118 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w108 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2119 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2119 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(4,true)),(false,(3,true),(0,false)),(false,(3,true),(0,true))] s4_2119 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w109 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2120 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2120 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2120 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2121 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2121 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(3,true),(0,true))] s4_2121 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w111 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2122 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2122 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2122 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w112 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2123 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2123 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2123 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons pc26w113 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2124 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2124 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2124 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0x33333232333332323333323233333232,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w114 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2125 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2125 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2125 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w118 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2126 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2126 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(5,true),(0,true))] s4_2126 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00fa00ff00fa00ff00fa00ff00fa,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w127 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w125 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2127 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2127 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2127 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w133 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w132 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2128 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2128 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_2128 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w144 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w142 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2129 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2129 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s4_2129 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffccffcc,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w157 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w155 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2130 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2130 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_2130 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w144 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w146 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2131 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2131 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s4_2131 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffccffcc,0xaaaaaaaa,0x0,0xf0f0f0f0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons pc0w157 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w155 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w159 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2132 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2132 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s4_2132 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w171 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w169 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2133 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2133 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_2133 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w144 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w177 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w176 rfl))))))))) (by decide +kernel)
theorem b4_2134 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2134 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s4_2134 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0x0,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0,0xcccccccc] (PetersenWireProjection.cons pc1w171 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w169 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w178 rfl))))))))) (by decide +kernel)
theorem b4_2135 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2135 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_2135 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w144 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w179 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2136 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2136 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2136 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w185 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons pc39w182 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w180 rfl))))))))) (by decide +kernel)
theorem b4_2137 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2137 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2137 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w133 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w187 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2138 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2138 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,true)),(false,(3,true),(0,true))] s4_2138 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x33333232333332323333323233333232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w96 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w190 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2139 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2139 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2139 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w191 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2140 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2140 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2140 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w192 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2141 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2141 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,true)),(false,(8,true),(0,true))] s4_2141 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffffff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w197 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
