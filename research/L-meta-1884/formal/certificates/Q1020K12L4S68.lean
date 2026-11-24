import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc26w4 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w6 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w3 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xddddddddddddddddcccccccccccccccc := PetersenWireProjection.derive 2 pc26w4 pc26w6 rfl rfl



private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl

private theorem pc26w12 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 pc26w10 pc26w12 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored1 stored5 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored2 stored5 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffaaffaaffaaffaaff00ff00ff00ff00 := PetersenWireProjection.derive 0 pc26w15 pc26w16 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc26w19 stored0 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffeeeeeeee : BitVec 256) = 0xffff0f0fffff0f0fffff0a0affff0a0a := PetersenWireProjection.derive 3 pc26w18 pc26w12 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 pc26w22 pc26w23 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeffffffffeeeeeeeeaaaaaaaaaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xf5f55555f5f55555f0f00000f0f00000 := PetersenWireProjection.derive 3 pc26w21 pc26w24 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffffffffffcccccccc00000000ffffffff00000000 : BitVec 256) = 0xffff5555ffff5555f0f05050f0f05050 := PetersenWireProjection.derive 1 pc26w27 pc26w28 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffff5555ffff5555f0f05050f0f05050 := PetersenWireProjection.derive 3 pc26w26 stored7 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w31 pc26w12 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored0 stored1 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffff5555ffff5555ffff5050ffff5050 := PetersenWireProjection.derive 3 pc26w30 pc26w32 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc26w35 pc26w12 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w34 pc26w36 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc26w35 pc26w39 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f00000f0f00000fafaaaaafafaaaaa := PetersenWireProjection.derive 3 pc26w38 pc26w24 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w35 stored0 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafa0000fafa0000fafa0000fafa0000 := PetersenWireProjection.derive 0 pc26w42 pc26w12 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 3 pc26w36 pc26w44 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafa0000fafa0000fafafafafafafafa := PetersenWireProjection.derive 3 pc26w41 pc26w43 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w44 pc26w12 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000fffffafafffffafa := PetersenWireProjection.derive 3 pc26w46 pc26w36 rfl rfl






private theorem pc18w53 : PetersenPackedPin.project tree18 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored185 stored187 rfl rfl
private theorem pc18w55 : PetersenPackedPin.project tree18 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored186 stored187 rfl rfl
private theorem pc18w52 : PetersenPackedPin.project tree18 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc18w53 pc18w55 rfl rfl

private theorem pc18w57 : PetersenPackedPin.project tree18 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffccccffffcccc := PetersenWireProjection.derive 3 stored188 stored191 rfl rfl
private theorem pc18w56 : PetersenPackedPin.project tree18 (0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0ffffffffccccccccf0f0f0f0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w52 pc18w57 rfl rfl







private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored38 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored38 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w66 pc3w68 rfl rfl

private theorem pc3w71 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w71 pc3w68 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored38 rfl rfl
private theorem pc3w69 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w70 pc3w73 rfl rfl

private theorem pc3w75 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl





private theorem pc17w81 : PetersenPackedPin.project tree17 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored169 stored173 rfl rfl
private theorem pc17w83 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored170 stored173 rfl rfl
private theorem pc17w80 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc17w81 pc17w83 rfl rfl

private theorem pc17w86 : PetersenPackedPin.project tree17 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored170 stored175 rfl rfl
private theorem pc17w85 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc17w86 stored173 rfl rfl
private theorem pc17w89 : PetersenPackedPin.project tree17 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored170 stored175 rfl rfl
private theorem pc17w88 : PetersenPackedPin.project tree17 (0xcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc17w89 stored169 rfl rfl
private theorem pc17w84 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff00ccccccccccccccccff00ff00ff00ff00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc17w85 pc17w88 rfl rfl





private theorem pc37w94 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl

private theorem pc37w93 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w94 stored65 rfl rfl


private theorem pc37w101 : PetersenPackedPin.project extra37 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f000000000 := PetersenWireProjection.derive 0 stored65 stored69 rfl rfl
private theorem pc37w103 : PetersenPackedPin.project extra37 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 0 stored66 stored69 rfl rfl
private theorem pc37w100 : PetersenPackedPin.project extra37 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 pc37w101 pc37w103 rfl rfl
private theorem pc37w105 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored66 stored71 rfl rfl
private theorem pc37w104 : PetersenPackedPin.project extra37 (0xcccccccc000000000000000000000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc37w105 stored65 rfl rfl
private theorem pc37w99 : PetersenPackedPin.project extra37 (0xff00ff00ff00ff00ff00ff00ccccccccff00ff00ff00ff00ff00ff00cccccccc : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 pc37w100 pc37w104 rfl rfl







private theorem pc21w114 : PetersenPackedPin.project tree21 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored297 stored300 rfl rfl
private theorem pc21w116 : PetersenPackedPin.project tree21 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored298 stored300 rfl rfl
private theorem pc21w113 : PetersenPackedPin.project tree21 (0xff00ff00ff00ff00ff00ff0000000000ff00ff00ff00ff00ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc21w114 pc21w116 rfl rfl

private theorem pc21w118 : PetersenPackedPin.project tree21 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored298 stored301 rfl rfl
private theorem pc21w117 : PetersenPackedPin.project tree21 (0xcccccccc000000000000000000000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc21w118 stored297 rfl rfl
private theorem pc21w112 : PetersenPackedPin.project tree21 (0xff00ff00ff00ff00ff00ff00ccccccccff00ff00ff00ff00ff00ff00cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc21w113 pc21w117 rfl rfl




private theorem pc32w124 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored24 stored26 rfl rfl

private theorem pc32w123 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0ffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w124 stored25 rfl rfl


private theorem pc32w129 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl

private theorem pc32w128 : PetersenPackedPin.project extra32 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w129 stored28 rfl rfl


private theorem pc32w136 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl
private theorem pc32w135 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a00000000000000000 := PetersenWireProjection.derive 0 pc32w136 stored24 rfl rfl
private theorem pc32w134 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w128 pc32w135 rfl rfl
private theorem pc32w139 : PetersenPackedPin.project extra32 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored24 stored29 rfl rfl
private theorem pc32w140 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w138 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccc00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xafafafafafafafafafaf0000afaf0000 := PetersenWireProjection.derive 2 pc32w139 pc32w140 rfl rfl
private theorem pc32w137 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccff00ff00ffffffffffffffffffffffffff00ff00 : BitVec 256) = 0xafafafafafafafafafaf0000afaf0000 := PetersenWireProjection.derive 3 pc32w138 stored28 rfl rfl
private theorem pc32w142 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w143 : PetersenPackedPin.project extra32 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored26 stored27 rfl rfl
private theorem pc32w141 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xff00ffffff00ffffff00ff00ff00ff00 := PetersenWireProjection.derive 2 pc32w142 pc32w143 rfl rfl
private theorem pc32w145 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored24 stored29 rfl rfl
private theorem pc32w144 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc32w145 stored28 rfl rfl
private theorem pc32w146 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w148 : PetersenPackedPin.project extra32 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored24 stored25 rfl rfl
private theorem pc32w147 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xafafa0a0afafa0a0afafa0a0afafa0a0 := PetersenWireProjection.derive 3 pc32w144 pc32w148 rfl rfl
private theorem pc32w150 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc32w140 stored24 rfl rfl
private theorem pc32w151 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w149 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffffffffffffffffffffffffffccffcc : BitVec 256) = 0xafafafafafafafafafafaaaaafafaaaa := PetersenWireProjection.derive 3 pc32w150 pc32w151 rfl rfl
private theorem pc32w154 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored28 rfl rfl
private theorem pc32w155 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w153 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ffffffffff00ff00ff00ff00ff00ff00ffffffffff00ff00 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 pc32w154 pc32w155 rfl rfl
private theorem pc32w152 : PetersenPackedPin.project extra32 (0xffccffccffccffccffffffffffccffccff00ff00ff00ff00ffffffffff00ff00 : BitVec 256) = 0xa0a0ffffa0a0ffffa0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc32w153 pc32w145 rfl rfl
private theorem pc32w158 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc32w159 : PetersenPackedPin.project extra32 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored25 stored29 rfl rfl
private theorem pc32w157 : PetersenPackedPin.project extra32 (0xccccccccccccccccffffffffffffffffcccccccc00000000ffffffff00000000 : BitVec 256) = 0xaaaaffffaaaaffffa0a0f0f0a0a0f0f0 := PetersenWireProjection.derive 1 pc32w158 pc32w159 rfl rfl
private theorem pc32w156 : PetersenPackedPin.project extra32 (0xffccffccffccffccffffffffffffffffffccffccff00ff00ffffffffff00ff00 : BitVec 256) = 0xaaaaffffaaaaffffa0a0f0f0a0a0f0f0 := PetersenWireProjection.derive 3 pc32w157 stored28 rfl rfl
private theorem pc32w162 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 stored25 stored26 rfl rfl
private theorem pc32w161 : PetersenPackedPin.project extra32 (0xffccffccffccffccffffffffffccffccffccffccffccffccffffffffffccffcc : BitVec 256) = 0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w162 pc32w151 rfl rfl
private theorem pc32w163 : PetersenPackedPin.project extra32 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored24 stored25 rfl rfl
private theorem pc32w160 : PetersenPackedPin.project extra32 (0xffccffccffccffccffffffffffffffffffccffccffccffccffffffffffccffcc : BitVec 256) = 0xaaaaffffaaaaffffaaaafafaaaaafafa := PetersenWireProjection.derive 3 pc32w161 pc32w163 rfl rfl
private theorem pc32w165 : PetersenPackedPin.project extra32 (0xffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 3 pc32w136 stored28 rfl rfl
private theorem pc32w166 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored26 rfl rfl
private theorem pc32w164 : PetersenPackedPin.project extra32 (0xffccffccffffffffffccffccff00ff00ffccffccffffffffffccffccff00ff00 : BitVec 256) = 0xaaaaaaaaaaaaaaaaffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w165 pc32w166 rfl rfl
private theorem pc32w168 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 3 pc32w128 pc32w145 rfl rfl
private theorem pc32w170 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored26 rfl rfl
private theorem pc32w169 : PetersenPackedPin.project extra32 (0xffffffff00000000ffffffff00000000ffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w170 pc32w166 rfl rfl
private theorem pc32w167 : PetersenPackedPin.project extra32 (0xffccffccffffffffffccffccffffffffffccffccffffffffff00ff00ff00ff00 : BitVec 256) = 0xaaaaa0a0aaaaa0a0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w168 pc32w169 rfl rfl
private theorem pc32w172 : PetersenPackedPin.project extra32 (0xffccffccffffffffffccffccffccffccffccffccffffffffffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc32w166 pc32w151 rfl rfl
private theorem pc32w171 : PetersenPackedPin.project extra32 (0xffccffccffffffffffccffccffffffffffccffccffffffffffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaafffffafafffffafa := PetersenWireProjection.derive 3 pc32w172 pc32w170 rfl rfl
private theorem pc3w174 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w175 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored34 stored35 rfl rfl
private theorem pc3w173 : PetersenPackedPin.project cycle3 (0xffffffffccccccccccccccccccccccccffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 3 pc3w174 pc3w175 rfl rfl



private theorem pc0w179 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w181 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w178 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w179 pc0w181 rfl rfl







private theorem pc1w191 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl
private theorem pc1w190 : PetersenPackedPin.project cycle1 (0x333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc1w191 stored57 rfl rfl

private theorem pc1w193 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored59 stored63 rfl rfl
private theorem pc1w189 : PetersenPackedPin.project cycle1 (0xffffffffccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 2 pc1w190 pc1w193 rfl rfl




private theorem pc0w200 : PetersenPackedPin.project cycle0 (0x33333333000000003333333300000000000000000000000000000000 : BitVec 256) = 0x3300 := PetersenWireProjection.derive 2 pc0w181 stored49 rfl rfl
private theorem pc0w199 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w200 pc0w179 rfl rfl
private theorem pc0w202 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w201 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w202 stored49 rfl rfl
private theorem pc0w204 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w203 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w204 pc0w202 rfl rfl


private theorem pc2w205 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl

private theorem pc2w210 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored41 stored43 rfl rfl

private theorem pc2w211 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w209 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffff00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w210 pc2w211 rfl rfl




private theorem pc0w217 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w202 stored51 rfl rfl
private theorem pc2w218 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w210 stored42 rfl rfl
private theorem pc2w219 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w211 stored43 rfl rfl
private theorem pc1w222 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc1w221 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffc0c0 := PetersenWireProjection.derive 3 pc1w222 stored59 rfl rfl
private theorem pc1w223 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w220 : PetersenPackedPin.project cycle1 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc1w221 pc1w223 rfl rfl


private theorem pc69w227 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored97 stored98 rfl rfl


private theorem pc69w228 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w226 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w227 pc69w228 rfl rfl




private theorem pc69w235 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored97 stored100 rfl rfl
private theorem pc2w238 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w237 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafa := PetersenWireProjection.derive 3 pc2w238 stored41 rfl rfl
private theorem pc2w239 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w236 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc2w237 pc2w239 rfl rfl
private theorem pc26w240 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
theorem b4_2856 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2856 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(5,false),(3,false)),(false,(1,true),(3,true))] s4_2856 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf0f00000f0f00000f0f00000f0f00000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xddddddddddddddddcccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2857 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2857 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false)),(false,(1,false),(7,false)),(false,(5,true),(0,true))] s4_2857 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf0f00000f0f00000f0f00000f0f00000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffaaffaaffaaffaaff00ff00ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2858 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2858 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true)),(false,(0,true),(3,true)),(false,(0,true),(6,true))] s4_2858 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0fffff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2859 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2859 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(5,false),(3,false)),(false,(1,true),(0,true))] s4_2859 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf5f55555f5f55555f0f00000f0f00000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2860 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2860 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true)),(false,(7,true),(3,true)),(false,(1,true),(0,true))] s4_2860 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555f0f05050f0f05050,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2861 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2861 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(1,true),(0,true)),(false,(0,true),(6,true))] s4_2861 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff5050ffff5050,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2862 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2862 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,false),(1,false)),(false,(1,true),(0,true))] s4_2862 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaaaa0000aaaa0000fafaf0f0fafaf0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2863 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2863 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,false),(5,false)),(false,(1,true),(0,true))] s4_2863 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf0f00000f0f00000fafaaaaafafaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2864 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2864 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true)),(false,(1,true),(3,true)),(false,(1,true),(0,true))] s4_2864 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xfafa0000fafa0000fafafafafafafafa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2865 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2865 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(0,true),(7,true)),(false,(0,true),(6,true))] s4_2865 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000fffffafafffffafa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2866 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2866 := by
  intro m le c
  apply rejects_sound tree18 i6 6 tgt small18 hot18 [] s4_2866 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0x0,0x0,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored192 (PetersenWireProjection.cons stored191 (PetersenWireProjection.cons pc18w56 (PetersenWireProjection.cons pc18w52 (PetersenWireProjection.cons stored190 (PetersenWireProjection.cons stored189 (PetersenWireProjection.cons stored188 (PetersenWireProjection.cons stored186 (PetersenWireProjection.cons stored185 rfl))))))))) (by decide +kernel)
theorem b4_2867 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2867 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2867 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2868 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2868 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2868 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))) (by decide +kernel)
theorem b4_2869 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2869 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2869 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w75 rfl))))))))) (by decide +kernel)
theorem b4_2870 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2870 := by
  intro m le c
  apply rejects_sound tree17 i6 6 tgt small17 hot17 [] s4_2870 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffffffff00000000,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons stored176 (PetersenWireProjection.cons stored175 (PetersenWireProjection.cons stored174 (PetersenWireProjection.cons pc17w84 (PetersenWireProjection.cons pc17w80 (PetersenWireProjection.cons stored172 (PetersenWireProjection.cons stored171 (PetersenWireProjection.cons stored170 (PetersenWireProjection.cons stored169 rfl))))))))) (by decide +kernel)
theorem b4_2871 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2871 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2871 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons pc37w99 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w93 (PetersenWireProjection.cons stored67 rfl))))))))) (by decide +kernel)
theorem b4_2872 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2872 := by
  intro m le c
  apply rejects_sound tree21 i6 6 tgt small21 hot21 [] s4_2872 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0xffffffff00000000,0x0,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xcccccccccccccccc] (PetersenWireProjection.cons stored303 (PetersenWireProjection.cons stored301 (PetersenWireProjection.cons stored302 (PetersenWireProjection.cons pc21w112 (PetersenWireProjection.cons stored299 (PetersenWireProjection.cons stored298 (PetersenWireProjection.cons stored297 (PetersenWireProjection.cons stored296 rfl)))))))) (by decide +kernel)
theorem b4_2873 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2873 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(5,false),(1,false)),(false,(1,true),(6,true))] s4_2873 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xfffff0f0fffff0f0ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w128 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w123 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2874 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2874 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(2,false)),(false,(0,true),(5,true)),(false,(2,false),(0,true))] s4_2874 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaa0a0aaaaa0a0aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xfffff0f0fffff0f0ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w134 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w123 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2875 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2875 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,false),(0,true)),(false,(5,true),(7,true)),(false,(1,true),(0,true))] s4_2875 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xafafafafafafafafafaf0000afaf0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w137 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2876 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2876 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(1,false),(3,false)),(false,(1,true),(5,true))] s4_2876 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xff00ffffff00ffffff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w144 (PetersenWireProjection.cons pc32w141 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2877 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2877 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,false),(0,true)),(false,(3,true),(5,true)),(false,(1,true),(0,true))] s4_2877 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xafafa0a0afafa0a0afafa0a0afafa0a0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w147 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w146 rfl))))))))) (by decide +kernel)
theorem b4_2878 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2878 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(4,true)),(false,(0,true),(3,true)),(false,(0,true),(2,true))] s4_2878 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xafafafafafafafafafafaaaaafafaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w149 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2879 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2879 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(1,false),(3,false)),(false,(1,true),(0,true))] s4_2879 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xa0a0ffffa0a0ffffa0a0a0a0a0a0a0a0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w152 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2880 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2880 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,true)),(false,(7,true),(3,true)),(false,(1,true),(0,true))] s4_2880 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaffffaaaaffffa0a0f0f0a0a0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w156 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2881 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2881 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(5,true),(0,true)),(false,(0,true),(2,true))] s4_2881 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaffffaaaaffffaaaafafaaaaafafa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w160 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2882 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2882 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,true)),(false,(7,true),(5,true)),(false,(1,true),(0,true))] s4_2882 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w164 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w140 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2883 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2883 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,true)),(false,(5,true),(3,true)),(false,(1,true),(0,true))] s4_2883 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaa0a0aaaaa0a0fffff0f0fffff0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w167 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2884 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2884 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(0,true),(7,true)),(false,(0,true),(2,true))] s4_2884 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaafffffafafffffafa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w171 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2885 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2885 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_2885 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w173 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w75 rfl))))))))) (by decide +kernel)
theorem b4_2886 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2886 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2886 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w178 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2887 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2887 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s4_2887 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffcccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w189 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2888 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2888 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2888 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w199 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2889 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2889 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2889 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w203 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w201 rfl))))))))) (by decide +kernel)
theorem b4_2890 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2890 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s4_2890 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaa0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w209 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w205 rfl))))))))) (by decide +kernel)
theorem b4_2891 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2891 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2891 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w217 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2892 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2892 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,false),(0,false))] s4_2892 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaa0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w219 (PetersenWireProjection.cons pc2w218 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2893 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2893 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(4,true))] s4_2893 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffcccc,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w220 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2894 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2894 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2894 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w226 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2895 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2895 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2895 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w226 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons pc69w235 rfl))))))))) (by decide +kernel)
theorem b4_2896 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2896 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2896 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w236 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2897 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2897 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s4_2897 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w240 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
