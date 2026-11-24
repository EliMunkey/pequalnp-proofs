import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
import Q1020K12L5S1
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc16w5 : PetersenPackedPin.project tree16 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored147 stored148 rfl rfl

private theorem pc16w4 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc16w5 stored149 rfl rfl
private theorem pc16w8 : PetersenPackedPin.project tree16 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored145 stored146 rfl rfl
private theorem pc16w3 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000ffffccccffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc16w4 pc16w8 rfl rfl





private theorem pc74w12 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl


private theorem pc74w18 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl

private theorem pc74w17 : PetersenPackedPin.project extra74 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc74w18 stored116 rfl rfl
private theorem pc74w16 : PetersenPackedPin.project extra74 (0xffffccccffff0000ffffccccffff0000ffffccccffff00000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 0 pc74w17 pc74w12 rfl rfl







private theorem pc35w29 : PetersenPackedPin.project extra35 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored219 stored222 rfl rfl

private theorem pc35w28 : PetersenPackedPin.project extra35 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w29 stored224 rfl rfl
private theorem pc35w32 : PetersenPackedPin.project extra35 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 2 stored217 stored218 rfl rfl
private theorem pc35w27 : PetersenPackedPin.project extra35 (0xffffccccffff0000ffffccccffff0000ffffffffffffffffffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w28 pc35w32 rfl rfl





private theorem pc26w38 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl

private theorem pc26w40 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc26w38 pc26w40 rfl rfl


private theorem pc26w44 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl

private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w44 stored3 rfl rfl




private theorem pc3w51 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl

private theorem pc3w53 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w50 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 pc3w51 pc3w53 rfl rfl

private theorem pc3w57 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w56 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w57 stored36 rfl rfl



private theorem pc35w63 : PetersenPackedPin.project extra35 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffffffff000000000000000000000000 := PetersenWireProjection.derive 0 stored217 stored218 rfl rfl
private theorem pc35w62 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w28 pc35w63 rfl rfl
private theorem pc16w65 : PetersenPackedPin.project tree16 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored146 stored149 rfl rfl
private theorem pc16w64 : PetersenPackedPin.project tree16 (0xffffffffffffffffffffccccffff0000ffffffffffffffffffffccccffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc16w65 pc16w5 rfl rfl
private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored36 stored39 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc3w67 stored34 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w71 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w69 : PetersenPackedPin.project extra26 (0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc26w70 pc26w71 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored1 stored3 rfl rfl
private theorem pc26w68 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffeeeeffffaaaaffffffffffffffffffffeeeeffffaaaa : BitVec 256) = 0xffffeeeeffffeeeeeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 pc26w69 pc26w72 rfl rfl



private theorem pc30w76 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl

private theorem pc30w75 : PetersenPackedPin.project extra30 (0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w76 stored13 rfl rfl


private theorem pc30w80 : PetersenPackedPin.project extra30 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored11 rfl rfl
private theorem pc30w74 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffcfcfffff0f0fffffffffffffffffffffcfcfffff0f0 : BitVec 256) = 0xfffffffffffffffffaf0faf0faf0faf0 := PetersenWireProjection.derive 3 pc30w75 pc30w80 rfl rfl
private theorem pc30w83 : PetersenPackedPin.project extra30 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w76 stored11 rfl rfl





private theorem pc32w89 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl

private theorem pc32w88 : PetersenPackedPin.project extra32 (0xffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 3 pc32w89 stored28 rfl rfl


private theorem pc32w93 : PetersenPackedPin.project extra32 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffff00ffffff00ffffff00ffffff00 := PetersenWireProjection.derive 3 stored25 stored27 rfl rfl
private theorem pc32w87 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffccffffff00ffffffffffffffffffffffccffffff00 : BitVec 256) = 0xffffffaaffffffaaffffff00ffffff00 := PetersenWireProjection.derive 3 pc32w88 pc32w93 rfl rfl
private theorem pc32w96 : PetersenPackedPin.project extra32 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffaaffaaffaaffaaff00ff00ff00ff00 := PetersenWireProjection.derive 3 pc32w89 stored27 rfl rfl





private theorem pc2w101 : PetersenPackedPin.project cycle2 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored43 stored44 rfl rfl

private theorem pc2w100 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc2w101 stored42 rfl rfl

private theorem pc2w106 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w105 : PetersenPackedPin.project cycle2 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc2w106 stored44 rfl rfl



private theorem pc26w111 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w40 stored0 rfl rfl
private theorem pc3w112 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w53 stored33 rfl rfl
private theorem pc30w114 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w114 stored8 rfl rfl
private theorem pc35w116 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored217 stored218 rfl rfl
private theorem pc35w115 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w28 pc35w116 rfl rfl
private theorem pc3w117 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w119 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl


private theorem pc108w120 : PetersenPackedPin.project extra108 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 stored312 stored313 rfl rfl

private theorem pc108w124 : PetersenPackedPin.project extra108 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored312 stored316 rfl rfl


private theorem pc108w126 : PetersenPackedPin.project extra108 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored314 stored315 rfl rfl
private theorem pc108w123 : PetersenPackedPin.project extra108 (0xffffffffffffffffffffffffffffffffffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w124 pc108w126 rfl rfl
private theorem pc108w129 : PetersenPackedPin.project extra108 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w126 stored316 rfl rfl







private theorem pc0w137 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w136 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w137 stored52 rfl rfl
private theorem pc0w141 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc0w140 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffcccc00000000ffff000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w136 pc0w141 rfl rfl



private theorem pc0w146 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w145 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffffffffffccccffffffffffff0000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 3 pc0w136 pc0w146 rfl rfl
private theorem pc0w148 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xff00 := PetersenWireProjection.derive 1 stored49 stored51 rfl rfl
private theorem pc0w147 : PetersenPackedPin.project cycle0 (0xffffccccffffffffffff0000ffffffffffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00 := PetersenWireProjection.derive 3 pc0w136 pc0w148 rfl rfl
private theorem pc3w150 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w149 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 pc3w51 pc3w150 rfl rfl
private theorem pc3w152 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w151 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w152 stored36 rfl rfl
private theorem pc0w154 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w153 : PetersenPackedPin.project cycle0 (0xffffffffffffccccffffffffffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w136 pc0w154 rfl rfl
private theorem pc0w155 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w154 stored50 rfl rfl
private theorem pc26w156 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w70 stored0 rfl rfl
private theorem pc26w158 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w157 : PetersenPackedPin.project extra26 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w158 stored3 rfl rfl
private theorem pc3w159 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w150 stored33 rfl rfl
private theorem pc30w161 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w160 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 pc30w161 stored8 rfl rfl
private theorem pc30w163 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w162 : PetersenPackedPin.project extra30 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff000f000f000f000 := PetersenWireProjection.derive 3 pc30w163 stored11 rfl rfl
private theorem pc32w165 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w164 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w165 stored24 rfl rfl
private theorem pc32w167 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl
private theorem pc32w166 : PetersenPackedPin.project extra32 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc32w167 stored27 rfl rfl
private theorem pc0w170 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored52 rfl rfl
private theorem pc0w169 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc0w170 stored49 rfl rfl
private theorem pc0w168 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffff0000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc0w169 pc0w137 rfl rfl
private theorem pc0w172 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl
private theorem pc0w171 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 pc0w172 stored49 rfl rfl
private theorem pc26w173 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc32w174 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc30w175 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
private theorem pc0w176 : PetersenPackedPin.project cycle0 (0xffffffffffffccccffffffffffff0000ffffffffffffccccffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w137 pc0w170 rfl rfl




private theorem pc34w182 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc34w181 : PetersenPackedPin.project extra34 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w182 stored19 rfl rfl
private theorem pc34w185 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w180 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 3 pc34w181 pc34w185 rfl rfl
private theorem pc34w187 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w188 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w186 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffcccc00000000ffffccccffffccccffffcccc00000000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 0 pc34w187 pc34w188 rfl rfl



private theorem pc26w192 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w70 stored1 rfl rfl
private theorem pc26w193 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffffccccffffcccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w43 pc26w158 rfl rfl
private theorem pc3w194 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w150 stored34 rfl rfl
private theorem pc3w195 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w56 pc3w152 rfl rfl
theorem b4_3108 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3108 := by
  intro m le c
  apply rejects_sound tree16 i6 6 tgt small16 hot16 [] s4_3108 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] (PetersenWireProjection.cons stored152 (PetersenWireProjection.cons stored148 (PetersenWireProjection.cons stored151 (PetersenWireProjection.cons stored150 (PetersenWireProjection.cons pc16w3 (PetersenWireProjection.cons stored147 (PetersenWireProjection.cons stored146 (PetersenWireProjection.cons stored145 rfl)))))))) (by decide +kernel)
theorem b4_3109 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3109 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3109 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w16 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w12 rfl))))))))) (by decide +kernel)
theorem b4_3110 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3110 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3110 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w28 (PetersenWireProjection.cons pc35w27 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3111 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3111 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,false)),(false,(7,false),(5,false)),(false,(3,true),(0,true))] s4_3111 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3112 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3112 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,false))] s4_3112 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f00000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w56 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w50 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3113 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3113 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3113 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w28 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons pc35w62 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3114 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3114 := by
  intro m le c
  apply rejects_sound tree16 i6 6 tgt small16 hot16 [] s4_3114 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] (PetersenWireProjection.cons stored152 (PetersenWireProjection.cons stored148 (PetersenWireProjection.cons stored151 (PetersenWireProjection.cons stored150 (PetersenWireProjection.cons pc16w4 (PetersenWireProjection.cons stored147 (PetersenWireProjection.cons stored146 (PetersenWireProjection.cons pc16w64 (PetersenWireProjection.cons stored145 rfl))))))))) (by decide +kernel)
theorem b4_3115 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3115 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(3,true),(4,true))] s4_3115 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffff00,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w56 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3116 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3116 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(2,true)),(false,(0,false),(2,true))] s4_3116 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffeeeeffffeeeeeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w68 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3117 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3117 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(0,true),(7,true)),(false,(0,false),(4,true))] s4_3117 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffaf0faf0faf0faf0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w74 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_3118 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3118 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(6,false)),(false,(0,true),(4,true)),(false,(0,false),(6,true))] s4_3118 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaffaaffaaffaaff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffaaffffffaaffffff00ffffff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w96 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w87 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3119 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3119 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(3,true),(4,true))] s4_3119 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffff00,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w105 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w100 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_3120 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3120 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3120 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w17 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w12 rfl))))))))) (by decide +kernel)
theorem b4_3121 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3121 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(1,true),(3,true)),(false,(1,true),(3,true))] s4_3121 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w111 rfl))))))))) (by decide +kernel)
theorem b4_3122 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3122 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3122 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w56 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w112 rfl))))))))) (by decide +kernel)
theorem b4_3123 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3123 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(3,true),(6,true)),(false,(1,true),(8,true))] s4_3123 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w113 rfl))))))))) (by decide +kernel)
theorem b4_3124 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3124 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3124 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w28 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 (PetersenWireProjection.cons pc35w115 rfl))))))))) (by decide +kernel)
theorem b4_3125 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3125 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3125 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w56 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w51 (PetersenWireProjection.cons pc3w117 rfl))))))))) (by decide +kernel)
theorem b4_3126 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3126 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,false)),(false,(3,true),(5,true)),(false,(1,true),(5,true))] s4_3126 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaffaaffaaffaaff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w96 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w119 (PetersenWireProjection.cons pc32w118 rfl))))))))) (by decide +kernel)
theorem b4_3127 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3127 := by
  intro m le c
  apply rejects_sound extra108 i6 5 tgt small108 hot108 [] s4_3127 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0x0,0xffffffffffffffff,0xffffffff00000000] (PetersenWireProjection.cons stored319 (PetersenWireProjection.cons stored315 (PetersenWireProjection.cons stored318 (PetersenWireProjection.cons stored317 (PetersenWireProjection.cons pc108w129 (PetersenWireProjection.cons stored314 (PetersenWireProjection.cons stored313 (PetersenWireProjection.cons pc108w123 (PetersenWireProjection.cons pc108w120 rfl))))))))) (by decide +kernel)
theorem b4_3128 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3128 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_3128 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w140 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_3129 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3129 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s4_3129 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons pc0w145 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_3130 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3130 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,true))] s4_3130 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xff00,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons pc0w147 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_3131 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3131 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false))] s4_3131 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xc0c0c0c0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w151 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w149 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3132 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3132 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_3132 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_3133 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3133 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_3133 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w155 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_3134 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3134 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3135 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3135 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(3,true),(7,true)),(false,(3,true),(1,true))] s4_3135 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w157 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w156 rfl))))))))) (by decide +kernel)
theorem b4_3136 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3136 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s4_3136 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w151 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w159 rfl))))))))) (by decide +kernel)
theorem b4_3137 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3137 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(6,true),(1,true)),(false,(8,true),(1,true))] s4_3137 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffff000f000f000f000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w162 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w160 rfl))))))))) (by decide +kernel)
theorem b4_3138 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3138 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,false)),(false,(3,true),(7,true)),(false,(5,true),(1,true))] s4_3138 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w166 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w164 rfl))))))))) (by decide +kernel)
theorem b4_3139 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3139 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s4_3139 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w168 rfl))))))))) (by decide +kernel)
theorem b4_3140 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3140 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s4_3140 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w171 rfl))))))))) (by decide +kernel)
theorem b4_3141 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3141 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(3,true),(7,true)),(false,(3,true),(1,true))] s4_3141 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w157 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons pc26w173 rfl))))))))) (by decide +kernel)
theorem b4_3142 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3142 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,false)),(false,(3,true),(7,true)),(false,(5,true),(1,true))] s4_3142 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w166 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w119 (PetersenWireProjection.cons pc32w174 rfl))))))))) (by decide +kernel)
theorem b4_3143 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3143 := by
  apply node_sound (nxt := [a6623,a6624])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_3 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_41 theta)
theorem b4_3144 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3144 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(6,true),(1,true)),(false,(8,true),(1,true))] s4_3144 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffff000f000f000f000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w162 (PetersenWireProjection.cons pc30w161 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w175 rfl))))))))) (by decide +kernel)
theorem b4_3145 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3145 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s4_3145 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons pc0w176 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w141 rfl))))))))) (by decide +kernel)
theorem b4_3146 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3146 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(0,true),(1,false))] s4_3146 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w186 (PetersenWireProjection.cons pc34w180 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_3147 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3147 := by
  apply node_sound (nxt := [a6625,a6626])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_4 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_42 theta)
theorem b4_3148 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3148 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(0,true),(3,true))] s4_3148 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w193 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w192 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3149 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3149 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_3149 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w195 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w194 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
