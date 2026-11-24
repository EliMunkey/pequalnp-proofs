import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc3w1 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl

private theorem pc3w0 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w1 stored33 rfl rfl

private theorem pc3w8 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl

private theorem pc3w7 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w8 stored36 rfl rfl
private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored33 stored36 rfl rfl
private theorem pc3w6 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 pc3w7 pc3w10 rfl rfl





private theorem pc30w15 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl

private theorem pc30w14 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w15 stored8 rfl rfl


private theorem pc30w22 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl

private theorem pc30w21 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffff0f000f000f000f00 := PetersenWireProjection.derive 3 pc30w22 stored11 rfl rfl
private theorem pc30w25 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w20 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffff000000000f000f00 := PetersenWireProjection.derive 1 pc30w21 pc30w25 rfl rfl




private theorem pc32w29 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl

private theorem pc32w28 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w29 stored24 rfl rfl


private theorem pc32w36 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored25 stored29 rfl rfl

private theorem pc32w35 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xff00ffaaff00ffaaff00ffaaff00ffaa := PetersenWireProjection.derive 3 pc32w36 stored27 rfl rfl
private theorem pc32w39 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w34 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xff00ff0aff00ff0aff00ff0aff00ff0a := PetersenWireProjection.derive 1 pc32w35 pc32w39 rfl rfl




private theorem pc35w43 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored217 stored222 rfl rfl


private theorem pc35w46 : PetersenPackedPin.project extra35 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored218 stored224 rfl rfl
private theorem pc35w42 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w43 pc35w46 rfl rfl

private theorem pc35w52 : PetersenPackedPin.project extra35 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored218 stored222 rfl rfl
private theorem pc35w51 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w52 stored224 rfl rfl
private theorem pc35w53 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored217 stored224 rfl rfl
private theorem pc35w50 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc35w51 pc35w53 rfl rfl





private theorem pc39w58 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored75 rfl rfl

private theorem pc39w57 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w58 stored73 rfl rfl

private theorem pc39w64 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored74 stored79 rfl rfl

private theorem pc39w63 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 pc39w64 stored76 rfl rfl
private theorem pc39w67 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w62 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 pc39w63 pc39w67 rfl rfl



private theorem pc3w71 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc32w73 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w74 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl


private theorem pc41w75 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl

private theorem pc41w79 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored92 rfl rfl

private theorem pc41w81 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored89 stored95 rfl rfl
private theorem pc41w78 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w79 pc41w81 rfl rfl

private theorem pc41w85 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffff0c0c0c0cffffffff0c0c0c0c := PetersenWireProjection.derive 3 pc41w81 stored92 rfl rfl
private theorem pc41w86 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 1 stored91 stored92 rfl rfl
private theorem pc41w84 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 pc41w85 pc41w86 rfl rfl



private theorem pc30w90 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc39w91 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl
private theorem pc39w93 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored73 stored79 rfl rfl
private theorem pc39w94 : PetersenPackedPin.project extra39 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored76 rfl rfl
private theorem pc39w92 : PetersenPackedPin.project extra39 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w93 pc39w94 rfl rfl


private theorem pc26w96 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl

private theorem pc26w95 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w96 stored0 rfl rfl


private theorem pc26w103 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w102 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w103 stored0 rfl rfl

private theorem pc26w101 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xcccccccccccccccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w102 stored3 rfl rfl


private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w109 stored33 rfl rfl
private theorem pc3w112 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w111 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w112 stored33 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w111 stored36 rfl rfl
private theorem pc30w114 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 pc30w114 stored8 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w116 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc : BitVec 256) = 0x550055000000000055005500 := PetersenWireProjection.derive 1 pc30w117 stored8 rfl rfl
private theorem pc30w115 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xffffffffffffffff0000000055005500 := PetersenWireProjection.derive 3 pc30w116 stored11 rfl rfl
private theorem pc32w119 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w119 stored24 rfl rfl
private theorem pc32w122 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored26 stored29 rfl rfl
private theorem pc32w121 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w122 stored24 rfl rfl
private theorem pc32w120 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xff00ff00ff00ff00ff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w121 stored27 rfl rfl
private theorem pc35w124 : PetersenPackedPin.project extra35 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored219 stored224 rfl rfl
private theorem pc35w123 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w43 pc35w124 rfl rfl
private theorem pc35w127 : PetersenPackedPin.project extra35 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored219 stored222 rfl rfl
private theorem pc35w126 : PetersenPackedPin.project extra35 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc35w127 stored217 rfl rfl
private theorem pc35w125 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w126 stored224 rfl rfl


private theorem pc37w129 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl

private theorem pc37w128 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w129 stored67 rfl rfl

private theorem pc37w135 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored66 stored71 rfl rfl
private theorem pc37w134 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc37w135 stored67 rfl rfl

private theorem pc37w133 : PetersenPackedPin.project extra37 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 pc37w134 stored68 rfl rfl



private theorem pc26w141 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w142 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc32w143 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc30w144 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc37w145 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl
private theorem pc37w147 : PetersenPackedPin.project extra37 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 stored67 stored71 rfl rfl
private theorem pc37w148 : PetersenPackedPin.project extra37 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored68 rfl rfl
private theorem pc37w146 : PetersenPackedPin.project extra37 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w147 pc37w148 rfl rfl
private theorem pc35w151 : PetersenPackedPin.project extra35 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored224 stored222 rfl rfl
private theorem pc35w150 : PetersenPackedPin.project extra35 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w151 stored219 rfl rfl
private theorem pc35w149 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc35w150 pc35w53 rfl rfl
private theorem pc35w153 : PetersenPackedPin.project extra35 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored217 stored222 rfl rfl
private theorem pc35w152 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w153 stored224 rfl rfl
private theorem pc35w155 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w151 stored218 rfl rfl
private theorem pc35w154 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc35w155 pc35w53 rfl rfl
private theorem pc35w158 : PetersenPackedPin.project extra35 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored218 stored224 rfl rfl
private theorem pc35w157 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc35w158 pc35w124 rfl rfl
private theorem pc35w156 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffffffffffff0000ffffccccffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w157 pc35w153 rfl rfl
private theorem pc35w161 : PetersenPackedPin.project extra35 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored219 stored224 rfl rfl
private theorem pc35w160 : PetersenPackedPin.project extra35 (0xffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 1 pc35w46 pc35w161 rfl rfl
private theorem pc35w159 : PetersenPackedPin.project extra35 (0xffff0000ffffffffffff0000ffff0000ffffccccffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w160 pc35w153 rfl rfl
private theorem pc3w162 : PetersenPackedPin.project cycle3 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w1 pc3w109 rfl rfl
private theorem pc3w164 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w163 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w164 stored36 rfl rfl
private theorem pc35w166 : PetersenPackedPin.project extra35 (0xffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 0 pc35w46 pc35w124 rfl rfl
private theorem pc35w165 : PetersenPackedPin.project extra35 (0xffffffffffff0000ffff0000ffff0000ffffffffffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w166 pc35w153 rfl rfl



private theorem pc20w170 : PetersenPackedPin.project tree20 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored304 stored306 rfl rfl


private theorem pc20w172 : PetersenPackedPin.project tree20 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored307 stored308 rfl rfl
private theorem pc20w169 : PetersenPackedPin.project tree20 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 pc20w170 pc20w172 rfl rfl
private theorem pc20w175 : PetersenPackedPin.project tree20 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc20w170 stored308 rfl rfl



private theorem pc26w181 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w182 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w180 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 pc26w181 pc26w182 rfl rfl
private theorem pc26w183 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w179 : PetersenPackedPin.project extra26 (0xffffffffffffaaaaffffffffffffaaaaffffffffffffeeeeffffffffffffeeee : BitVec 256) = 0xffffffffffffffffcfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w180 pc26w183 rfl rfl
private theorem pc26w185 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w184 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w185 stored3 rfl rfl
private theorem pc3w187 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored36 stored39 rfl rfl
private theorem pc3w186 : PetersenPackedPin.project cycle3 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 pc3w187 stored35 rfl rfl
private theorem pc30w190 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w189 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 3 pc30w190 stored13 rfl rfl
private theorem pc30w191 : PetersenPackedPin.project extra30 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored11 rfl rfl
private theorem pc30w188 : PetersenPackedPin.project extra30 (0xfffffffffffff0f0fffffffffffff0f0fffffffffffffcfcfffffffffffffcfc : BitVec 256) = 0xffffffffffffffffaaaaaaaaffaaffaa := PetersenWireProjection.derive 3 pc30w189 pc30w191 rfl rfl
private theorem pc30w192 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w190 stored11 rfl rfl
private theorem pc32w195 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w194 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ffccffccffccffccffccffccffccffcc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 3 pc32w195 stored28 rfl rfl
private theorem pc32w196 : PetersenPackedPin.project extra32 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored26 stored27 rfl rfl
private theorem pc32w193 : PetersenPackedPin.project extra32 (0xffffffffffffff00ffffffffffffff00ffffffffffffffccffffffffffffffcc : BitVec 256) = 0xffffffffffffffffff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w194 pc32w196 rfl rfl
private theorem pc32w197 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w195 stored27 rfl rfl
private theorem pc20w199 : PetersenPackedPin.project tree20 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 stored305 stored308 rfl rfl
private theorem pc20w198 : PetersenPackedPin.project tree20 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc20w170 pc20w199 rfl rfl
private theorem pc26w201 : PetersenPackedPin.project extra26 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored1 stored3 rfl rfl
private theorem pc26w200 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffaaaaffffaaaaffffffffffffffffffffeeeeffffeeee : BitVec 256) = 0xefefeeeeefefeeeeefefeeeeefefeeee := PetersenWireProjection.derive 3 pc26w180 pc26w201 rfl rfl
private theorem pc3w202 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc3w187 stored34 rfl rfl
private theorem pc30w204 : PetersenPackedPin.project extra30 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored11 rfl rfl
private theorem pc30w203 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffff0f0fffff0f0fffffffffffffffffffffcfcfffffcfc : BitVec 256) = 0xfffffffffffffffff0f0f0f0fff0fff0 := PetersenWireProjection.derive 3 pc30w189 pc30w204 rfl rfl
private theorem pc32w206 : PetersenPackedPin.project extra32 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffff00ffffff00ffffff00ffffff00 := PetersenWireProjection.derive 3 stored25 stored27 rfl rfl
private theorem pc32w205 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffff00ffffff00ffffffffffffffffffffffccffffffcc : BitVec 256) = 0xffffff0affffff0affffff0affffff0a := PetersenWireProjection.derive 3 pc32w194 pc32w206 rfl rfl



private theorem pc74w208 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl

private theorem pc74w212 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored113 stored119 rfl rfl

private theorem pc74w211 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc74w212 stored116 rfl rfl



private theorem pc26w218 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w96 stored1 rfl rfl
private theorem pc3w219 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w109 stored34 rfl rfl
private theorem pc30w220 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc30w114 stored9 rfl rfl
theorem b4_3024 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3024 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3024 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w6 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w0 rfl))))))))) (by decide +kernel)
theorem b4_3025 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3025 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false)),(false,(0,true),(8,true))] s4_3025 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff000000000f000f00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w20 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w14 rfl))))))))) (by decide +kernel)
theorem b4_3026 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3026 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false)),(false,(0,true),(5,true))] s4_3026 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff0aff00ff0aff00ff0aff00ff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w28 rfl))))))))) (by decide +kernel)
theorem b4_3027 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3027 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3027 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w50 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 (PetersenWireProjection.cons pc35w42 rfl))))))))) (by decide +kernel)
theorem b4_3028 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3028 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_3028 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons pc39w62 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w57 rfl))))))))) (by decide +kernel)
theorem b4_3029 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3029 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3029 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w6 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w72 (PetersenWireProjection.cons pc3w71 rfl))))))))) (by decide +kernel)
theorem b4_3030 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3030 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false)),(false,(0,true),(5,true))] s4_3030 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff0aff00ff0aff00ff0aff00ff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w74 (PetersenWireProjection.cons pc32w73 rfl))))))))) (by decide +kernel)
theorem b4_3031 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3031 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_3031 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons pc41w84 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w78 (PetersenWireProjection.cons pc41w75 rfl))))))))) (by decide +kernel)
theorem b4_3032 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3032 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(0,false),(4,false)),(false,(0,true),(8,true))] s4_3032 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff000000000f000f00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w20 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w15 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w90 rfl))))))))) (by decide +kernel)
theorem b4_3033 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3033 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_3033 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons pc39w62 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons pc39w92 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w91 rfl))))))))) (by decide +kernel)
theorem b4_3034 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3034 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_3034 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons pc39w62 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons pc39w58 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w91 rfl))))))))) (by decide +kernel)
theorem b4_3035 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3035 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3036 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3036 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(5,false),(0,false)),(false,(0,true),(3,true))] s4_3036 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w101 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w95 rfl))))))))) (by decide +kernel)
theorem b4_3037 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3037 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s4_3037 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w108 rfl))))))))) (by decide +kernel)
theorem b4_3038 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3038 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(4,false),(0,false)),(false,(0,true),(8,true))] s4_3038 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000055005500,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w115 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w113 rfl))))))))) (by decide +kernel)
theorem b4_3039 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3039 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(6,true)),(false,(1,false),(0,false)),(false,(0,true),(5,true))] s4_3039 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w118 rfl))))))))) (by decide +kernel)
theorem b4_3040 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3040 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3040 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w125 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 (PetersenWireProjection.cons pc35w123 rfl))))))))) (by decide +kernel)
theorem b4_3041 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3041 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_3041 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons pc37w133 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w128 rfl))))))))) (by decide +kernel)
theorem b4_3042 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3042 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(5,false),(0,false)),(false,(0,true),(3,true))] s4_3042 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w101 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w142 (PetersenWireProjection.cons pc26w141 rfl))))))))) (by decide +kernel)
theorem b4_3043 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3043 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(6,true)),(false,(1,false),(0,false)),(false,(0,true),(5,true))] s4_3043 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w74 (PetersenWireProjection.cons pc32w143 rfl))))))))) (by decide +kernel)
theorem b4_3044 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3044 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(4,false),(0,false)),(false,(0,true),(8,true))] s4_3044 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000055005500,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w115 (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w144 rfl))))))))) (by decide +kernel)
theorem b4_3045 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3045 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_3045 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons pc37w133 (PetersenWireProjection.cons pc37w146 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w145 rfl))))))))) (by decide +kernel)
theorem b4_3046 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3046 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3046 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w152 (PetersenWireProjection.cons pc35w149 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3047 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3047 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3047 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w152 (PetersenWireProjection.cons pc35w154 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3048 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3048 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3048 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w152 (PetersenWireProjection.cons pc35w156 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3049 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3049 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3049 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w152 (PetersenWireProjection.cons pc35w159 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3050 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3050 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_3050 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3051 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3051 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3051 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w152 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons pc35w165 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3052 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3052 := by
  intro m le c
  apply rejects_sound tree20 i6 6 tgt small20 hot20 [] s4_3052 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000,0x0,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc,0xcccccccccccccccc,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored311 (PetersenWireProjection.cons stored306 (PetersenWireProjection.cons stored310 (PetersenWireProjection.cons stored309 (PetersenWireProjection.cons pc20w175 (PetersenWireProjection.cons stored307 (PetersenWireProjection.cons pc20w169 (PetersenWireProjection.cons stored305 (PetersenWireProjection.cons stored304 rfl))))))))) (by decide +kernel)
theorem b4_3053 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3053 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true)),(false,(0,false),(8,true))] s4_3053 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffcfcfcccccfcfcccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w184 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w179 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3054 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3054 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(1,true))] s4_3054 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffccffcc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w186 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3055 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3055 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true)),(false,(0,false),(2,true))] s4_3055 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w192 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w188 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_3056 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3056 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(0,true),(4,true)),(false,(0,false),(8,true))] s4_3056 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffffffffffffffffff0aff0aff0aff0a,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w197 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w193 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3057 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3057 := by
  intro m le c
  apply rejects_sound tree20 i6 6 tgt small20 hot20 [] s4_3057 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000,0x0,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc,0xffff0000ffff0000,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored311 (PetersenWireProjection.cons stored306 (PetersenWireProjection.cons stored310 (PetersenWireProjection.cons stored309 (PetersenWireProjection.cons pc20w175 (PetersenWireProjection.cons stored307 (PetersenWireProjection.cons stored305 (PetersenWireProjection.cons pc20w198 (PetersenWireProjection.cons stored304 rfl))))))))) (by decide +kernel)
theorem b4_3058 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3058 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true)),(false,(0,false),(2,true))] s4_3058 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xefefeeeeefefeeeeefefeeeeefefeeee,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w184 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w200 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3059 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3059 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(4,true))] s4_3059 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffff00,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w202 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3060 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3060 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true)),(false,(0,false),(4,true))] s4_3060 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w192 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w203 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_3061 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3061 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(0,true),(4,true)),(false,(0,false),(6,true))] s4_3061 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffff0affffff0affffff0affffff0a,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w197 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w205 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3062 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3062 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3062 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w211 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w208 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_3063 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3063 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(1,true)),(false,(1,true),(3,true))] s4_3063 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w184 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w218 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3064 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3064 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s4_3064 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w219 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3065 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3065 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(3,true)),(false,(1,true),(8,true))] s4_3065 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w192 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w220 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
