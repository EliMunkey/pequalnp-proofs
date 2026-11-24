import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc29w2 : PetersenPackedPin.project extra29 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored156 stored154 rfl rfl

private theorem pc29w1 : PetersenPackedPin.project extra29 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 pc29w2 stored155 rfl rfl



private theorem pc29w10 : PetersenPackedPin.project extra29 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored153 stored154 rfl rfl
private theorem pc29w11 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl
private theorem pc29w9 : PetersenPackedPin.project extra29 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc29w10 pc29w11 rfl rfl





private theorem pc3w17 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w16 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w17 stored36 rfl rfl


private theorem pc3w23 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w24 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w22 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w23 pc3w24 rfl rfl

private theorem pc3w27 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w27 stored36 rfl rfl
private theorem pc3w29 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w29 stored37 rfl rfl
private theorem pc29w30 : PetersenPackedPin.project extra29 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 pc29w2 stored159 rfl rfl
private theorem pc29w33 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w32 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w33 stored155 rfl rfl
private theorem pc29w31 : PetersenPackedPin.project extra29 (0xccccccccccccccccccccccccccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc29w32 pc29w10 rfl rfl


private theorem pc74w34 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl





private theorem pc74w43 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc74w42 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w43 stored114 rfl rfl
private theorem pc74w45 : PetersenPackedPin.project extra74 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored113 stored119 rfl rfl
private theorem pc74w41 : PetersenPackedPin.project extra74 (0xccccccccccccccccccccccccccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 1 pc74w42 pc74w45 rfl rfl

private theorem pc74w47 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl


private theorem pc69w50 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored97 stored99 rfl rfl

private theorem pc69w49 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc69w50 stored98 rfl rfl



private theorem pc69w58 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored98 stored99 rfl rfl
private theorem pc69w57 : PetersenPackedPin.project extra69 (0xffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w58 stored97 rfl rfl

private theorem pc69w59 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored100 rfl rfl
private theorem pc69w56 : PetersenPackedPin.project extra69 (0xccccccccccccccccffffffff00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w57 pc69w59 rfl rfl








private theorem pc1w70 : PetersenPackedPin.project cycle1 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x30303030 := PetersenWireProjection.derive 1 stored58 stored63 rfl rfl
private theorem pc1w72 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w69 : PetersenPackedPin.project cycle1 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xcfcfcccc := PetersenWireProjection.derive 2 pc1w70 pc1w72 rfl rfl
private theorem pc1w73 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc1w68 : PetersenPackedPin.project cycle1 (0xccccccccccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc1w69 pc1w73 rfl rfl








private theorem pc2w82 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w84 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w81 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w82 pc2w84 rfl rfl

private theorem pc3w87 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w88 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w86 : PetersenPackedPin.project cycle3 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 pc3w87 pc3w88 rfl rfl
private theorem pc74w90 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored113 stored117 rfl rfl
private theorem pc74w91 : PetersenPackedPin.project extra74 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff := PetersenWireProjection.derive 1 stored114 stored117 rfl rfl
private theorem pc74w89 : PetersenPackedPin.project extra74 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 pc74w90 pc74w91 rfl rfl
private theorem pc74w93 : PetersenPackedPin.project extra74 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored114 stored119 rfl rfl
private theorem pc74w92 : PetersenPackedPin.project extra74 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc74w93 pc74w43 rfl rfl
private theorem pc3w95 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w94 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w95 stored37 rfl rfl







private theorem pc0w104 : PetersenPackedPin.project cycle0 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored55 rfl rfl
private theorem pc0w103 : PetersenPackedPin.project cycle0 (0x3333333333333333000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w104 stored49 rfl rfl
private theorem pc0w106 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w102 : PetersenPackedPin.project cycle0 (0xccccccccccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 2 pc0w103 pc0w106 rfl rfl

private theorem pc74w109 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored113 stored115 rfl rfl
private theorem pc74w108 : PetersenPackedPin.project extra74 (0xccccccccccccccccffffffffffffffffcccccccc00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w109 pc74w93 rfl rfl


private theorem pc32w110 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl




private theorem pc32w118 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl

private theorem pc32w119 : PetersenPackedPin.project extra32 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored25 stored29 rfl rfl
private theorem pc32w117 : PetersenPackedPin.project extra32 (0xccccccccccccccccffffffffffffffffcccccccc00000000ffffffff00000000 : BitVec 256) = 0xaaaaffffaaaaffffa0a0f0f0a0a0f0f0 := PetersenWireProjection.derive 1 pc32w118 pc32w119 rfl rfl

private theorem pc29w123 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc29w124 : PetersenPackedPin.project extra29 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored155 stored154 rfl rfl
private theorem pc29w122 : PetersenPackedPin.project extra29 (0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc29w123 pc29w124 rfl rfl
private theorem pc29w126 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w33 stored153 rfl rfl
private theorem pc29w125 : PetersenPackedPin.project extra29 (0xccccccccccccccccffffffffffffffffccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc29w126 pc29w124 rfl rfl
private theorem pc29w129 : PetersenPackedPin.project extra29 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffccccccccffffffffcccccccc := PetersenWireProjection.derive 3 stored156 stored159 rfl rfl
private theorem pc29w128 : PetersenPackedPin.project extra29 (0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000 : BitVec 256) = 0x333333330000000000000000 := PetersenWireProjection.derive 2 pc29w129 stored155 rfl rfl
private theorem pc29w127 : PetersenPackedPin.project extra29 (0xcccccccccfcfcfcfcccccccccccccccccccccccccfcfcfcfcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w128 stored154 rfl rfl
private theorem pc29w131 : PetersenPackedPin.project extra29 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc29w123 pc29w2 rfl rfl
private theorem pc29w132 : PetersenPackedPin.project extra29 (0x3030303030303030303030303030303030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored159 stored154 rfl rfl
private theorem pc29w130 : PetersenPackedPin.project extra29 (0xcccccccccfcfcfcfcccccccccfcfcfcfcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc29w131 pc29w132 rfl rfl



private theorem pc61w136 : PetersenPackedPin.project extra61 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored287 stored291 rfl rfl

private theorem pc61w138 : PetersenPackedPin.project extra61 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored288 stored291 rfl rfl
private theorem pc61w135 : PetersenPackedPin.project extra61 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 0 pc61w136 pc61w138 rfl rfl





private theorem pc0w147 : PetersenPackedPin.project cycle0 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored51 stored55 rfl rfl
private theorem pc0w146 : PetersenPackedPin.project cycle0 (0x3333333300000000333333330000000000000000000000000000000000000000 : BitVec 256) = 0x33000000 := PetersenWireProjection.derive 0 pc0w147 stored49 rfl rfl
private theorem pc0w148 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w145 : PetersenPackedPin.project cycle0 (0xccccccccffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w146 pc0w148 rfl rfl
private theorem pc3w150 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w149 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w150 stored38 rfl rfl
private theorem pc3w152 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w153 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w151 : PetersenPackedPin.project cycle3 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0x30303030 := PetersenWireProjection.derive 1 pc3w152 pc3w153 rfl rfl
private theorem pc3w155 : PetersenPackedPin.project cycle3 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored36 stored39 rfl rfl
private theorem pc3w154 : PetersenPackedPin.project cycle3 (0xccccffffccccccccccccffffccccccccccccffffccccccccccccffffcccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 pc3w88 pc3w155 rfl rfl
private theorem pc3w156 : PetersenPackedPin.project cycle3 (0xccccffffccccffffccccccccccccccccccccffffccccffffcccccccccccccccc : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 pc3w24 pc3w155 rfl rfl




private theorem pc397w161 : PetersenPackedPin.project extra397 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored242 stored247 rfl rfl
private theorem pc397w163 : PetersenPackedPin.project extra397 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored243 stored247 rfl rfl
private theorem pc397w160 : PetersenPackedPin.project extra397 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc397w161 pc397w163 rfl rfl



private theorem pc397w168 : PetersenPackedPin.project extra397 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 stored241 stored246 rfl rfl
private theorem pc397w170 : PetersenPackedPin.project extra397 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored247 stored246 rfl rfl
private theorem pc397w167 : PetersenPackedPin.project extra397 (0xccccffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 pc397w168 pc397w170 rfl rfl
private theorem pc397w172 : PetersenPackedPin.project extra397 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored243 stored246 rfl rfl
private theorem pc397w171 : PetersenPackedPin.project extra397 (0x333333330000000000000000000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc397w172 stored242 rfl rfl
private theorem pc397w166 : PetersenPackedPin.project extra397 (0xccccffffccccffffccccccccccccffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 pc397w167 pc397w171 rfl rfl

private theorem pc3w174 : PetersenPackedPin.project cycle3 (0xccccffffccccffffccccffffccccffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 pc3w152 pc3w155 rfl rfl



private theorem pc107w179 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored163 rfl rfl
private theorem pc107w178 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w179 stored161 rfl rfl

private theorem pc107w181 : PetersenPackedPin.project extra107 (0xffff000000000000ffff000000000000ffff000000000000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored163 stored167 rfl rfl
private theorem pc107w177 : PetersenPackedPin.project extra107 (0xffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w178 pc107w181 rfl rfl



private theorem pc107w187 : PetersenPackedPin.project extra107 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored166 rfl rfl
private theorem pc107w186 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w187 stored161 rfl rfl
private theorem pc107w189 : PetersenPackedPin.project extra107 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored167 stored166 rfl rfl
private theorem pc107w185 : PetersenPackedPin.project extra107 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w186 pc107w189 rfl rfl



private theorem pc34w193 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl

private theorem pc34w192 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w193 stored17 rfl rfl




private theorem pc34w201 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w200 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w201 stored16 rfl rfl
private theorem pc34w203 : PetersenPackedPin.project extra34 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored19 stored22 rfl rfl
private theorem pc34w199 : PetersenPackedPin.project extra34 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w200 pc34w203 rfl rfl

private theorem pc61w206 : PetersenPackedPin.project extra61 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored286 stored291 rfl rfl
private theorem pc61w205 : PetersenPackedPin.project extra61 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 2 pc61w206 pc61w136 rfl rfl






private theorem pc26w213 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored4 rfl rfl
private theorem pc26w215 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 1 stored1 stored4 rfl rfl
private theorem pc26w212 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 1 pc26w213 pc26w215 rfl rfl


private theorem pc26w218 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl

private theorem pc26w220 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w217 : PetersenPackedPin.project extra26 (0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc26w218 pc26w220 rfl rfl
private theorem pc26w223 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w222 : PetersenPackedPin.project extra26 (0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaffffffffffffffffeeeeeeeeaaaaaaaa : BitVec 256) = 0xffff0a0affff0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 3 pc26w217 pc26w223 rfl rfl
private theorem pc26w225 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc26w224 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w225 stored1 rfl rfl
private theorem pc26w227 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w226 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc26w227 pc26w220 rfl rfl
private theorem pc26w229 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored0 stored3 rfl rfl
private theorem pc26w230 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w228 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xfcfcfcfcfcfcfcfccccccccccccccccc := PetersenWireProjection.derive 0 pc26w229 pc26w230 rfl rfl
private theorem pc26w232 : PetersenPackedPin.project extra26 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored2 stored4 rfl rfl
private theorem pc26w231 : PetersenPackedPin.project extra26 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0ffffffff00000000 := PetersenWireProjection.derive 0 pc26w213 pc26w232 rfl rfl
private theorem pc26w234 : PetersenPackedPin.project extra26 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored0 stored5 rfl rfl
private theorem pc26w235 : PetersenPackedPin.project extra26 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored2 stored5 rfl rfl
private theorem pc26w233 : PetersenPackedPin.project extra26 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfff0fff0fff0fff0ff00ff00ff00ff00 := PetersenWireProjection.derive 0 pc26w234 pc26w235 rfl rfl
private theorem pc26w237 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored0 stored2 rfl rfl
private theorem pc26w236 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaffffffffeeeeeeeeffffffffaaaaaaaa : BitVec 256) = 0xafaf0f0fafaf0f0faaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w226 pc26w237 rfl rfl
private theorem pc26w240 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w239 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f000000000000000000000 := PetersenWireProjection.derive 0 pc26w240 stored0 rfl rfl
private theorem pc26w238 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafa0000fafa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w226 pc26w239 rfl rfl
private theorem pc26w243 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w244 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w242 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0f0fffff0f0faaaa0a0aaaaa0a0a := PetersenWireProjection.derive 2 pc26w243 pc26w244 rfl rfl
private theorem pc26w241 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffff0f0fffff0f0faaaa0a0aaaaa0a0a := PetersenWireProjection.derive 3 pc26w242 stored7 rfl rfl
theorem b4_2814 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2814 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2814 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w9 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w1 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2815 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2815 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2815 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w16 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2816 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2816 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2816 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2817 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2817 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,false))] s4_2817 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w28 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2818 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2818 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2818 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w9 (PetersenWireProjection.cons pc29w30 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2819 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2819 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2819 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w31 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2820 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2820 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2820 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w41 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w34 rfl))))))))) (by decide +kernel)
theorem b4_2821 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2821 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2821 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w41 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w47 (PetersenWireProjection.cons pc74w34 rfl))))))))) (by decide +kernel)
theorem b4_2822 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2822 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2822 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w56 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w49 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2823 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2823 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2823 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons pc1w68 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2824 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2824 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2824 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w81 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2825 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2825 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true))] s4_2825 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xcccc,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w16 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2826 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2826 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2826 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w92 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons pc74w89 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_2827 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2827 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true))] s4_2827 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xcccc,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w94 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2828 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2828 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s4_2828 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xffffcccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2829 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2829 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2829 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w108 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_2830 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2830 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,true)),(false,(7,true),(3,true)),(false,(1,true),(0,true))] s4_2830 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffa0a0f0f0a0a0f0f0,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w117 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w110 rfl))))))))) (by decide +kernel)
theorem b4_2831 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2831 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2831 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w122 (PetersenWireProjection.cons pc29w30 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2832 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2832 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2832 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w125 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2833 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2833 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2833 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w127 (PetersenWireProjection.cons pc29w30 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2834 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2834 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2834 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w130 (PetersenWireProjection.cons pc29w30 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2835 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2835 := by
  intro m le c
  apply rejects_sound extra61 i6 5 tgt small61 hot61 [] s4_2835 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0x0,0x0,0xcccccccccccccccc,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored293 (PetersenWireProjection.cons stored292 (PetersenWireProjection.cons stored294 (PetersenWireProjection.cons stored290 (PetersenWireProjection.cons stored289 (PetersenWireProjection.cons stored288 (PetersenWireProjection.cons pc61w135 (PetersenWireProjection.cons stored287 (PetersenWireProjection.cons stored286 rfl))))))))) (by decide +kernel)
theorem b4_2836 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2836 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2836 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w145 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2837 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2837 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,true))] s4_2837 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x30303030,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w151 (PetersenWireProjection.cons pc3w149 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2838 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2838 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2839 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2839 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(1,false))] s4_2839 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xcc00cc,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w154 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w16 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2840 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2840 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(4,false))] s4_2840 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w156 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w16 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2841 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2841 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(4,false))] s4_2841 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff0000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w156 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2842 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2842 := by
  intro m le c
  apply rejects_sound extra397 i5 4 tgt small397 hot397 [] s4_2842 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xffffffff,0xffff0000,0xff00ff00,0x0,0x0,0xf0f0f0f0,0xffffffff] (PetersenWireProjection.cons stored248 (PetersenWireProjection.cons stored246 (PetersenWireProjection.cons pc397w166 (PetersenWireProjection.cons stored245 (PetersenWireProjection.cons stored244 (PetersenWireProjection.cons pc397w160 (PetersenWireProjection.cons stored243 (PetersenWireProjection.cons stored242 (PetersenWireProjection.cons stored241 rfl))))))))) (by decide +kernel)
theorem b4_2843 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2843 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(2,false))] s4_2843 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf000f0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w174 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2844 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2844 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_2844 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xffffffffffffffff,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons pc107w185 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons pc107w177 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_2845 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2845 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2845 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w199 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w192 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2846 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2846 := by
  intro m le c
  apply rejects_sound extra61 i6 5 tgt small61 hot61 [] s4_2846 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0x0,0x0,0xffffffffffffffff,0xcccccccccccccccc,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored293 (PetersenWireProjection.cons stored292 (PetersenWireProjection.cons stored295 (PetersenWireProjection.cons pc61w205 (PetersenWireProjection.cons stored290 (PetersenWireProjection.cons stored289 (PetersenWireProjection.cons stored288 (PetersenWireProjection.cons stored287 (PetersenWireProjection.cons stored286 rfl))))))))) (by decide +kernel)
theorem b4_2847 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2847 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(5,false),(7,false)),(false,(1,true),(7,true))] s4_2847 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff00000000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w217 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w212 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2848 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2848 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(7,false),(5,false)),(false,(1,true),(0,true))] s4_2848 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0a0a0a0a0a0a0a0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w222 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2849 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2849 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(1,false),(5,false)),(false,(1,true),(2,true))] s4_2849 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfafafafafafafafaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w226 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w224 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2850 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2850 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,false)),(false,(1,false),(5,false)),(false,(3,true),(1,true))] s4_2850 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xfcfcfcfcfcfcfcfccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w226 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w228 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2851 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2851 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(1,false),(5,false)),(false,(7,true),(1,true))] s4_2851 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffffffff0f0f0f0ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w226 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w231 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2852 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2852 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,false)),(false,(5,false),(1,false)),(false,(5,true),(1,true))] s4_2852 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfff0fff0fff0fff0ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w226 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w233 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2853 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2853 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(5,false),(1,false)),(false,(1,true),(0,true))] s4_2853 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xafaf0f0fafaf0f0faaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w236 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2854 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2854 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(1,true)),(false,(6,false),(0,true))] s4_2854 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xfafa0000fafa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfafafafafafafafaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w238 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w224 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2855 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2855 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,true)),(false,(1,true),(7,true)),(false,(1,true),(0,true))] s4_2855 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0faaaa0a0aaaaa0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w241 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
