import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc3w4 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w3 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w4 stored36 rfl rfl


private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w10 pc3w11 rfl rfl





private theorem pc26w18 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl

private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w18 stored3 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffffccccffffcccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w17 pc26w21 rfl rfl


private theorem pc26w24 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xffff0000ffff0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w21 pc26w18 rfl rfl

private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w27 : PetersenPackedPin.project cycle3 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w28 stored37 rfl rfl
private theorem pc3w29 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored34 stored37 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff00ff00ff00ffccffccff00ff00ff00ff00ff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 pc3w27 pc3w29 rfl rfl





private theorem pc74w36 : PetersenPackedPin.project extra74 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff := PetersenWireProjection.derive 1 stored114 stored117 rfl rfl
private theorem pc74w38 : PetersenPackedPin.project extra74 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0xcccc0000cccc := PetersenWireProjection.derive 1 stored115 stored117 rfl rfl
private theorem pc74w35 : PetersenPackedPin.project extra74 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff00000000 : BitVec 256) = 0xffff0000ffff := PetersenWireProjection.derive 3 pc74w36 pc74w38 rfl rfl
private theorem pc74w39 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored113 stored117 rfl rfl
private theorem pc74w34 : PetersenPackedPin.project extra74 (0xff00ff00ff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 pc74w35 pc74w39 rfl rfl


private theorem pc74w43 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl
private theorem pc74w44 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl
private theorem pc74w42 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w43 pc74w44 rfl rfl

private theorem pc3w47 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored33 stored37 rfl rfl
private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 1 pc3w47 pc3w29 rfl rfl
private theorem pc3w49 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w48 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w49 stored37 rfl rfl



private theorem pc76w53 : PetersenPackedPin.project extra76 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored195 stored199 rfl rfl

private theorem pc76w52 : PetersenPackedPin.project extra76 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 pc76w53 stored194 rfl rfl
private theorem pc76w57 : PetersenPackedPin.project extra76 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored193 stored199 rfl rfl
private theorem pc76w51 : PetersenPackedPin.project extra76 (0xffffffffffffffffffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc76w52 pc76w57 rfl rfl



private theorem pc76w62 : PetersenPackedPin.project extra76 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored194 stored199 rfl rfl
private theorem pc76w63 : PetersenPackedPin.project extra76 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored195 stored199 rfl rfl
private theorem pc76w61 : PetersenPackedPin.project extra76 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc76w62 pc76w63 rfl rfl

private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w28 stored34 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w68 stored35 rfl rfl



private theorem pc37w70 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl

private theorem pc37w73 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl
private theorem pc37w75 : PetersenPackedPin.project extra37 (0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 0 pc37w73 stored65 rfl rfl



private theorem pc37w80 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored65 stored71 rfl rfl
private theorem pc37w81 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 0 stored66 stored71 rfl rfl
private theorem pc37w79 : PetersenPackedPin.project extra37 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 pc37w80 pc37w81 rfl rfl

private theorem pc3w83 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w84 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w10 stored35 rfl rfl
private theorem pc3w85 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w83 stored34 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w87 stored1 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl



private theorem pc32w92 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl

private theorem pc32w95 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl

private theorem pc32w97 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl


private theorem pc32w102 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl
private theorem pc32w103 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl
private theorem pc32w101 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w102 pc32w103 rfl rfl

private theorem pc74w105 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl
private theorem pc74w106 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl
private theorem pc74w107 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w11 stored36 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w109 pc3w10 rfl rfl







private theorem pc1w119 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc1w120 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w118 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xccccc0c0 := PetersenWireProjection.derive 3 pc1w119 pc1w120 rfl rfl
private theorem pc1w121 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w117 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w118 pc1w121 rfl rfl

private theorem pc3w123 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w9 pc3w4 rfl rfl







private theorem pc73w133 : PetersenPackedPin.project extra73 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored130 stored131 rfl rfl
private theorem pc73w132 : PetersenPackedPin.project extra73 (0xffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w133 stored129 rfl rfl
private theorem pc73w135 : PetersenPackedPin.project extra73 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored130 stored135 rfl rfl
private theorem pc73w136 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored131 stored135 rfl rfl
private theorem pc73w134 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w135 pc73w136 rfl rfl
private theorem pc73w131 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccc00000000ccccccccffffffffcccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w132 pc73w134 rfl rfl

private theorem pc74w139 : PetersenPackedPin.project extra74 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored119 rfl rfl
private theorem pc74w138 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 2 pc74w139 pc74w106 rfl rfl




private theorem pc75w142 : PetersenPackedPin.project extra75 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored212 stored211 rfl rfl



private theorem pc75w149 : PetersenPackedPin.project extra75 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored209 stored211 rfl rfl
private theorem pc75w150 : PetersenPackedPin.project extra75 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored210 stored212 rfl rfl
private theorem pc75w148 : PetersenPackedPin.project extra75 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 pc75w149 pc75w150 rfl rfl





private theorem pc34w154 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl



private theorem pc34w161 : PetersenPackedPin.project extra34 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 1 stored16 stored22 rfl rfl
private theorem pc34w162 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w160 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0fffff0f0fffff0f0 := PetersenWireProjection.derive 2 pc34w161 pc34w162 rfl rfl

private theorem pc3w165 : PetersenPackedPin.project cycle3 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored34 stored36 rfl rfl
private theorem pc3w166 : PetersenPackedPin.project cycle3 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored35 stored36 rfl rfl
private theorem pc3w164 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xff00ffcc := PetersenWireProjection.derive 2 pc3w165 pc3w166 rfl rfl
private theorem pc3w169 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored36 stored39 rfl rfl
private theorem pc3w168 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w11 pc3w169 rfl rfl
private theorem pc3w167 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccc0000cccccccccccccccccccccccccccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w168 pc3w10 rfl rfl
private theorem pc3w170 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w173 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w172 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w173 stored38 rfl rfl
private theorem pc3w174 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored38 rfl rfl
private theorem pc3w171 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 1 pc3w172 pc3w174 rfl rfl
private theorem pc3w177 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w176 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w177 stored38 rfl rfl
private theorem pc3w175 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 1 pc3w176 pc3w174 rfl rfl
private theorem pc1w179 : PetersenPackedPin.project cycle1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored62 rfl rfl
private theorem pc1w180 : PetersenPackedPin.project cycle1 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored58 stored62 rfl rfl
private theorem pc1w178 : PetersenPackedPin.project cycle1 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 2 pc1w179 pc1w180 rfl rfl
private theorem pc1w181 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w182 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc1w184 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored62 rfl rfl
private theorem pc1w183 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 pc1w180 pc1w184 rfl rfl
private theorem pc3w186 : PetersenPackedPin.project cycle3 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored38 rfl rfl
private theorem pc3w187 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored38 rfl rfl
private theorem pc3w185 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w186 pc3w187 rfl rfl
private theorem pc1w188 : PetersenPackedPin.project cycle1 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc1w181 stored61 rfl rfl
private theorem pc3w189 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w49 pc3w68 rfl rfl
private theorem pc3w190 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w174 pc3w186 rfl rfl
private theorem pc3w191 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w49 pc3w28 rfl rfl
private theorem pc3w192 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w10 stored38 rfl rfl
private theorem pc1w194 : PetersenPackedPin.project cycle1 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored59 stored63 rfl rfl
private theorem pc1w193 : PetersenPackedPin.project cycle1 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 3 pc1w194 stored62 rfl rfl
private theorem pc1w196 : PetersenPackedPin.project cycle1 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored62 stored63 rfl rfl
private theorem pc1w195 : PetersenPackedPin.project cycle1 (0xccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc1w181 pc1w196 rfl rfl
private theorem pc3w197 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w49 pc3w11 rfl rfl
theorem b4_2730 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2730 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2730 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w3 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2731 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2731 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(0,true),(3,true))] s4_2731 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2732 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2732 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2732 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2733 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2733 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2733 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w42 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons pc74w34 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_2734 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2734 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2734 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w46 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2735 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2735 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2735 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w27 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2736 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2736 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2736 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2737 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2737 := by
  intro m le c
  apply rejects_sound extra76 i5 4 tgt small76 hot76 [] s4_2737 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0x0,0xcccccccc,0xff00ff00,0xaaaaaaaa,0xf0f0f0f0,0x0,0x0] (PetersenWireProjection.cons stored200 (PetersenWireProjection.cons pc76w61 (PetersenWireProjection.cons stored198 (PetersenWireProjection.cons stored197 (PetersenWireProjection.cons stored196 (PetersenWireProjection.cons stored195 (PetersenWireProjection.cons stored194 (PetersenWireProjection.cons pc76w51 (PetersenWireProjection.cons stored193 rfl))))))))) (by decide +kernel)
theorem b4_2738 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2738 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2738 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2739 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2739 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2739 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w67 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2740 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2740 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2740 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons pc37w79 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons pc37w75 (PetersenWireProjection.cons pc37w73 (PetersenWireProjection.cons pc37w70 (PetersenWireProjection.cons stored67 rfl))))))))) (by decide +kernel)
theorem b4_2741 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2741 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2741 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w84 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2742 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2742 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2742 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w84 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2743 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2743 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2743 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2744 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2744 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(6,true),(8,true))] s4_2744 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2745 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2745 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(6,true),(8,true))] s4_2745 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons pc26w90 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2746 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2746 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false)),(false,(2,true),(8,true))] s4_2746 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w101 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w97 (PetersenWireProjection.cons pc32w95 (PetersenWireProjection.cons pc32w92 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2747 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2747 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2747 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w42 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons pc74w107 (PetersenWireProjection.cons pc74w106 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w105 rfl))))))))) (by decide +kernel)
theorem b4_2748 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2748 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2748 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w108 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2749 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2749 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_2749 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w108 (PetersenWireProjection.cons pc3w83 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2750 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2750 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2750 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w117 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2751 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2751 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2751 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w123 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w84 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2752 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2752 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2752 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w131 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2753 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2753 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2753 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w138 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w105 rfl))))))))) (by decide +kernel)
theorem b4_2754 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2754 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2754 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w138 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w106 (PetersenWireProjection.cons pc74w105 rfl))))))))) (by decide +kernel)
theorem b4_2755 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2755 := by
  intro m le c
  apply rejects_sound extra75 i6 5 tgt small75 hot75 [] s4_2755 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffffffffffff,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored216 (PetersenWireProjection.cons pc75w148 (PetersenWireProjection.cons stored211 (PetersenWireProjection.cons stored215 (PetersenWireProjection.cons stored214 (PetersenWireProjection.cons stored213 (PetersenWireProjection.cons pc75w142 (PetersenWireProjection.cons stored210 (PetersenWireProjection.cons stored209 rfl))))))))) (by decide +kernel)
theorem b4_2756 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2756 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,true)),(false,(5,true),(3,true)),(false,(1,true),(0,true))] s4_2756 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaa0a0aaaaa0a0fffff0f0fffff0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w160 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w154 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2757 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2757 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true)),(false,(0,true),(4,true))] s4_2757 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ffcc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w167 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w164 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2758 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2758 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2758 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w167 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w109 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2759 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2759 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,false))] s4_2759 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xc0c0c0c,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w49 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w171 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w170 rfl))))))))) (by decide +kernel)
theorem b4_2760 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2760 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,false))] s4_2760 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w49 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w175 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w170 rfl))))))))) (by decide +kernel)
theorem b4_2761 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2761 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2761 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w181 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w178 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2762 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2762 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2762 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w181 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w178 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w182 rfl))))))))) (by decide +kernel)
theorem b4_2763 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2763 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2763 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w49 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w172 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w170 rfl))))))))) (by decide +kernel)
theorem b4_2764 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2764 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,false),(2,false))] s4_2764 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xff00ff00,0x0,0xffff0000,0xf0f00000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w181 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w183 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2765 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2765 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_2765 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w49 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w185 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w170 rfl))))))))) (by decide +kernel)
theorem b4_2766 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2766 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(4,false))] s4_2766 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xff00ff00,0x0,0xffff0000,0xf0f00000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w181 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w188 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w183 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2767 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2767 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2767 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w189 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w172 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2768 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2768 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2768 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w191 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w190 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2769 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2769 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2769 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w191 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2770 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2770 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(4,false),(1,true))] s4_2770 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x33330000,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w195 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w193 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2771 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2771 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2771 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w197 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
