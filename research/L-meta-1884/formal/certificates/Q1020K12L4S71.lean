import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc26w0 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl

private theorem pc26w3 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl







private theorem pc41w11 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl


private theorem pc41w14 : PetersenPackedPin.project extra41 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33333333333333330000000000000000 := PetersenWireProjection.derive 1 stored90 stored95 rfl rfl
private theorem pc41w10 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff3333333300000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w11 pc41w14 rfl rfl
private theorem pc41w17 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl




private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w23 stored0 rfl rfl


private theorem pc30w25 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl

private theorem pc30w24 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w25 stored8 rfl rfl

private theorem pc30w29 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl




private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w37 pc26w38 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xfffffffffffffffffafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w35 pc26w38 rfl rfl


private theorem pc3w40 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl

private theorem pc3w43 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w46 stored34 rfl rfl







private theorem pc32w52 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl

private theorem pc32w55 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl

private theorem pc32w58 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl
private theorem pc32w57 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 3 pc32w58 stored25 rfl rfl






private theorem pc34w64 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl

private theorem pc34w67 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl

private theorem pc34w70 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w69 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w70 stored17 rfl rfl




private theorem pc41w77 : PetersenPackedPin.project extra41 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored90 rfl rfl
private theorem pc41w76 : PetersenPackedPin.project extra41 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc41w77 stored89 rfl rfl
private theorem pc32w79 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored24 stored26 rfl rfl
private theorem pc32w78 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w79 stored25 rfl rfl
private theorem pc34w81 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w80 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w81 stored17 rfl rfl
private theorem pc32w82 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w84 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored26 rfl rfl
private theorem pc32w83 : PetersenPackedPin.project extra32 (0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w84 stored25 rfl rfl


private theorem pc74w85 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl

private theorem pc74w88 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored113 stored119 rfl rfl

private theorem pc74w91 : PetersenPackedPin.project extra74 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 1 stored115 stored119 rfl rfl
private theorem pc74w90 : PetersenPackedPin.project extra74 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w91 stored114 rfl rfl




private theorem pc32w98 : PetersenPackedPin.project extra32 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 1 stored26 stored29 rfl rfl
private theorem pc32w97 : PetersenPackedPin.project extra32 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w98 stored25 rfl rfl
private theorem pc34w100 : PetersenPackedPin.project extra34 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored18 stored22 rfl rfl
private theorem pc34w99 : PetersenPackedPin.project extra34 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffff5050ffff5050ffff5050ffff5050 := PetersenWireProjection.derive 3 pc34w100 stored17 rfl rfl
private theorem pc3w102 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w101 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w102 stored34 rfl rfl
private theorem pc32w104 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl
private theorem pc32w103 : PetersenPackedPin.project extra32 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w104 stored25 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w105 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0 := PetersenWireProjection.derive 3 pc34w106 stored17 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w109 stored34 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 pc30w113 stored8 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f000f000f0f0f0f0f000f000 := PetersenWireProjection.derive 0 pc30w112 pc30w25 rfl rfl
private theorem pc34w114 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w117 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w116 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w117 stored16 rfl rfl
private theorem pc34w118 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc34w115 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc34w116 pc34w118 rfl rfl
private theorem pc74w119 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl
private theorem pc74w120 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 0 pc74w88 pc74w119 rfl rfl


private theorem pc116w121 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored106 rfl rfl

private theorem pc116w124 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored111 rfl rfl

private theorem pc116w128 : PetersenPackedPin.project extra116 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored107 stored111 rfl rfl
private theorem pc116w127 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc116w128 stored105 rfl rfl
private theorem pc116w130 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored106 stored107 rfl rfl
private theorem pc116w126 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 0 pc116w127 pc116w130 rfl rfl






private theorem pc1w135 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl

private theorem pc1w138 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl

private theorem pc1w141 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl
private theorem pc1w140 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w141 stored58 rfl rfl




private theorem pc74w149 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl
private theorem pc74w148 : PetersenPackedPin.project extra74 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w149 stored114 rfl rfl
private theorem pc74w150 : PetersenPackedPin.project extra74 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored113 stored115 rfl rfl
private theorem pc74w147 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w148 pc74w150 rfl rfl
private theorem pc26w151 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc32w153 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w152 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc32w153 stored24 rfl rfl
private theorem pc34w154 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc26w156 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w155 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff0f0f00000f0f0000 := PetersenWireProjection.derive 3 pc26w156 stored2 rfl rfl
private theorem pc32w157 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc32w158 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 3 pc32w58 stored26 rfl rfl
private theorem pc32w160 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored26 rfl rfl
private theorem pc32w159 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffff0000f0f00000f0f0 := PetersenWireProjection.derive 1 pc32w157 pc32w160 rfl rfl
private theorem pc26w161 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w38 stored2 rfl rfl
private theorem pc74w162 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc32w163 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc34w164 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc26w167 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w166 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xddddccccddddccccddddccccddddcccc := PetersenWireProjection.derive 3 pc26w167 stored3 rfl rfl
private theorem pc26w168 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w165 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xcdcdcccccdcdcccccdcdcccccdcdcccc := PetersenWireProjection.derive 1 pc26w166 pc26w168 rfl rfl
theorem b4_2982 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2982 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(3,true),(1,true))] s4_2982 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons pc26w0 rfl))))))))) (by decide +kernel)
theorem b4_2983 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2983 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2983 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w17 (PetersenWireProjection.cons pc41w10 rfl))))))))) (by decide +kernel)
theorem b4_2984 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2984 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(1,true),(3,true)),(false,(1,true),(4,true))] s4_2984 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons pc26w22 rfl))))))))) (by decide +kernel)
theorem b4_2985 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2985 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(3,true),(6,true)),(false,(1,true),(7,true))] s4_2985 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w29 (PetersenWireProjection.cons pc30w24 rfl))))))))) (by decide +kernel)
theorem b4_2986 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2986 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(3,true),(7,true)),(false,(1,true),(4,true))] s4_2986 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons pc26w35 rfl))))))))) (by decide +kernel)
theorem b4_2987 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2987 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true)),(false,(8,true),(0,false))] s4_2987 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xfffffffffffffffffafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons pc26w39 rfl))))))))) (by decide +kernel)
theorem b4_2988 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2988 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_2988 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons pc3w43 (PetersenWireProjection.cons pc3w40 rfl))))))))) (by decide +kernel)
theorem b4_2989 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2989 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(0,false),(1,false)),(false,(0,true),(6,true))] s4_2989 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0a0affff0a0affff0a0affff0a0a,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w57 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_2990 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2990 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,false)),(false,(0,true),(6,true))] s4_2990 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffffaaaaffffaaaa,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w69 (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_2991 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2991 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2991 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons pc41w76 (PetersenWireProjection.cons pc41w17 (PetersenWireProjection.cons pc41w11 rfl))))))))) (by decide +kernel)
theorem b4_2992 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2992 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(0,false),(7,false)),(false,(0,true),(6,true))] s4_2992 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0f0fffff0f0fffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w78 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_2993 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2993 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(0,false),(3,false)),(false,(0,true),(6,true))] s4_2993 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000fffff0f0fffff0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w80 (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_2994 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2994 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(4,true)),(false,(0,false),(3,false)),(false,(0,true),(6,true))] s4_2994 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000fffff0f0fffff0f0,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w83 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons pc32w55 rfl))))))))) (by decide +kernel)
theorem b4_2995 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2995 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2995 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w90 (PetersenWireProjection.cons pc74w88 (PetersenWireProjection.cons pc74w85 rfl))))))))) (by decide +kernel)
theorem b4_2996 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2996 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,true)),(false,(5,true),(3,true)),(false,(1,true),(6,true))] s4_2996 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff5555ffff5555ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w97 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_2997 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2997 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(0,true)),(false,(5,true),(7,true)),(false,(1,true),(6,true))] s4_2997 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff5050ffff5050ffff5050ffff5050,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w99 (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_2998 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2998 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_2998 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w101 (PetersenWireProjection.cons pc3w43 (PetersenWireProjection.cons pc3w40 rfl))))))))) (by decide +kernel)
theorem b4_2999 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2999 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(6,false)),(false,(5,true),(3,true)),(false,(1,true),(6,true))] s4_2999 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w103 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_3000 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3000 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(5,true),(7,true)),(false,(1,true),(6,true))] s4_3000 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w105 (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_3001 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3001 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_3001 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w108 (PetersenWireProjection.cons pc3w107 (PetersenWireProjection.cons pc3w43 rfl))))))))) (by decide +kernel)
theorem b4_3002 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3002 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,true),(3,false)),(false,(4,true),(7,true))] s4_3002 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f000f000f0f0f0f0f000f000,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons pc30w29 (PetersenWireProjection.cons pc30w110 rfl))))))))) (by decide +kernel)
theorem b4_3003 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3003 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(4,true),(6,true)),(false,(1,true),(7,true))] s4_3003 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w25 (PetersenWireProjection.cons pc30w29 (PetersenWireProjection.cons pc30w110 rfl))))))))) (by decide +kernel)
theorem b4_3004 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3004 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(6,true),(8,true))] s4_3004 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000aaaa0000aaaa0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w115 (PetersenWireProjection.cons pc34w114 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_3005 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3005 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(1,true),(7,true)),(false,(1,true),(8,true))] s4_3005 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w118 (PetersenWireProjection.cons pc34w114 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_3006 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3006 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3006 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w120 (PetersenWireProjection.cons pc74w119 (PetersenWireProjection.cons pc74w85 rfl))))))))) (by decide +kernel)
theorem b4_3007 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3007 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s4_3007 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w126 (PetersenWireProjection.cons pc116w124 (PetersenWireProjection.cons pc116w121 rfl))))))))) (by decide +kernel)
theorem b4_3008 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3008 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3009 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3009 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_3009 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc,0xf0f0f0f0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w140 (PetersenWireProjection.cons pc1w138 (PetersenWireProjection.cons pc1w135 rfl))))))))) (by decide +kernel)
theorem b4_3010 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3010 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3010 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w147 (PetersenWireProjection.cons pc74w88 (PetersenWireProjection.cons pc74w85 rfl))))))))) (by decide +kernel)
theorem b4_3011 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3011 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3011 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w119 (PetersenWireProjection.cons pc74w88 (PetersenWireProjection.cons pc74w85 rfl))))))))) (by decide +kernel)
theorem b4_3012 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3012 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(7,true),(1,true)),(false,(4,true),(2,true))] s4_3012 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w151 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons pc26w22 rfl))))))))) (by decide +kernel)
theorem b4_3013 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3013 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(1,true),(3,true)),(false,(6,true),(4,true))] s4_3013 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xfafafafafafafafafafafafafafafafa,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons pc32w152 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_3014 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3014 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(1,true),(7,true)),(false,(6,true),(8,true))] s4_3014 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w154 (PetersenWireProjection.cons pc34w116 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_3015 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3015 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,false)),(false,(0,true),(8,true))] s4_3015 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0f0f00000f0f0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w155 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons pc26w35 rfl))))))))) (by decide +kernel)
theorem b4_3016 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3016 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,false)),(false,(0,true),(8,true))] s4_3016 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w158 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w157 rfl))))))))) (by decide +kernel)
theorem b4_3017 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3017 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(4,true)),(false,(0,false),(3,false)),(false,(0,true),(8,true))] s4_3017 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000f0f00000f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w159 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons pc32w55 rfl))))))))) (by decide +kernel)
theorem b4_3018 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3018 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(7,true),(3,true)),(false,(1,true),(8,true))] s4_3018 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w161 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons pc26w35 rfl))))))))) (by decide +kernel)
theorem b4_3019 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3019 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true)),(false,(4,true),(0,false))] s4_3019 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w161 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons pc26w39 rfl))))))))) (by decide +kernel)
theorem b4_3020 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3020 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3020 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons pc74w162 (PetersenWireProjection.cons pc74w119 (PetersenWireProjection.cons pc74w88 (PetersenWireProjection.cons pc74w85 rfl))))))))) (by decide +kernel)
theorem b4_3021 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3021 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(1,true),(7,true)),(false,(6,true),(8,true))] s4_3021 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w163 (PetersenWireProjection.cons pc32w82 (PetersenWireProjection.cons pc32w55 (PetersenWireProjection.cons pc32w52 rfl))))))))) (by decide +kernel)
theorem b4_3022 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3022 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(1,true),(3,true)),(false,(6,true),(4,true))] s4_3022 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfafafafafafafafafafafafafafafafa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w164 (PetersenWireProjection.cons pc34w154 (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons pc34w64 rfl))))))))) (by decide +kernel)
theorem b4_3023 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3023 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false)),(false,(0,true),(3,true))] s4_3023 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcdcdcccccdcdcccccdcdcccccdcdcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w165 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w22 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
