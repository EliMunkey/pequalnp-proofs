import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc0w0 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored49 stored55 rfl rfl

private theorem pc0w5 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 stored51 stored55 rfl rfl

private theorem pc0w4 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w5 stored50 rfl rfl
private theorem pc0w3 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffff00000000cccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w4 stored49 rfl rfl






private theorem pc2w12 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl

private theorem pc2w16 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w15 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 pc2w16 stored41 rfl rfl







private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl

private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w24 stored0 rfl rfl

private theorem pc26w29 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w29 stored0 rfl rfl






private theorem pc30w36 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl

private theorem pc30w35 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 pc30w36 stored8 rfl rfl

private theorem pc30w41 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x55005500550055005500550055005500 := PetersenWireProjection.derive 2 stored10 stored14 rfl rfl
private theorem pc30w40 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffff55005500ffffffff55005500 := PetersenWireProjection.derive 3 pc30w41 stored8 rfl rfl






private theorem pc41w47 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl


private theorem pc41w51 : PetersenPackedPin.project extra41 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 stored90 stored95 rfl rfl
private theorem pc41w50 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w51 stored91 rfl rfl




private theorem pc26w59 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w59 stored0 rfl rfl
private theorem pc30w61 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w60 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w61 stored8 rfl rfl


private theorem pc37w63 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl

private theorem pc37w62 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w63 stored67 rfl rfl

private theorem pc37w68 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored66 stored71 rfl rfl
private theorem pc37w67 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 pc37w68 stored67 rfl rfl




private theorem pc37w74 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl
private theorem pc37w76 : PetersenPackedPin.project extra37 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored65 stored66 rfl rfl
private theorem pc37w75 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffff00000000ffffffff00000000cccccccc : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 pc37w67 pc37w76 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w79 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffccccccccccccccccffffffffcccccccc : BitVec 256) = 0xfffff5f5fffff5f5fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w78 pc26w79 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffffcccccccc : BitVec 256) = 0xfffffffffffffffff5f5f0f0f5f5f0f0 := PetersenWireProjection.derive 3 pc26w82 pc26w83 rfl rfl
private theorem pc26w85 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffcccccccccccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w78 pc26w85 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xfffffffffffffffffafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w82 pc26w87 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfffffffffffffffffffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w89 stored0 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w80 pc26w29 rfl rfl
private theorem pc26w92 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0fafafafafafafafa := PetersenWireProjection.derive 3 pc26w80 pc26w92 rfl rfl
private theorem pc26w94 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w93 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffbbbbbbbbaaaaaaaabbbbbbbbaaaaaaaa : BitVec 256) = 0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w80 pc26w94 rfl rfl
private theorem pc26w96 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w95 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0fafaf0f0fafaf0f0fafaf0f0fafa := PetersenWireProjection.derive 3 pc26w80 pc26w96 rfl rfl
private theorem pc0w99 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w98 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w99 stored50 rfl rfl
private theorem pc0w97 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccc000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w98 stored49 rfl rfl
private theorem pc2w101 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w100 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w101 stored41 rfl rfl
private theorem pc2w103 : PetersenPackedPin.project cycle2 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w101 stored42 rfl rfl
private theorem pc2w102 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w103 stored41 rfl rfl
private theorem pc0w105 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w104 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w105 stored49 rfl rfl
private theorem pc0w106 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc41w108 : PetersenPackedPin.project extra41 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccc0000000000000000 := PetersenWireProjection.derive 0 stored90 stored95 rfl rfl
private theorem pc41w107 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w108 stored91 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w110 stored0 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xffffffffaa00aa00ffffffffaa00aa00 := PetersenWireProjection.derive 3 pc30w112 stored8 rfl rfl


private theorem pc32w114 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl

private theorem pc32w113 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w114 stored24 rfl rfl


private theorem pc32w119 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xfafafafafafafafaf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w119 stored24 rfl rfl



private theorem pc41w125 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl
private theorem pc41w127 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored89 stored95 rfl rfl
private theorem pc41w126 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w127 stored91 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w87 stored0 rfl rfl
private theorem pc41w129 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w125 pc41w127 rfl rfl


private theorem pc3w131 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl

private theorem pc3w130 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w131 stored33 rfl rfl

private theorem pc3w136 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w135 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w136 stored33 rfl rfl




private theorem pc26w142 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffeeeeeeeeffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffffafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w23 pc26w87 rfl rfl
private theorem pc30w144 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w143 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfffffffff000f000fffffffff000f000 := PetersenWireProjection.derive 3 pc30w144 stored8 rfl rfl
private theorem pc30w145 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffcfcfcfcfffffffff0f0f0f0 : BitVec 256) = 0xfffffffffaaafaaafffffffffaaafaaa := PetersenWireProjection.derive 3 pc30w35 pc30w144 rfl rfl
private theorem pc30w147 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc30w148 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored9 stored10 rfl rfl
private theorem pc30w146 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 3 pc30w147 pc30w148 rfl rfl
private theorem pc30w149 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w151 : PetersenPackedPin.project extra30 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa := PetersenWireProjection.derive 1 stored10 stored14 rfl rfl
private theorem pc30w150 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xffffffff00aa00aaffffffff00aa00aa := PetersenWireProjection.derive 3 pc30w147 pc30w151 rfl rfl
private theorem pc30w153 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w152 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff3f3f3f3f3f3f3f3f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00f000f0ffffffff00f000f0 := PetersenWireProjection.derive 3 pc30w147 pc30w153 rfl rfl
private theorem pc26w154 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafaf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w80 pc26w85 rfl rfl
private theorem pc30w156 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w155 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffa0a0a0a0ffffffffa0a0a0a0 := PetersenWireProjection.derive 3 pc30w147 pc30w156 rfl rfl
theorem b4_2940 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2940 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s4_2940 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffccffcc] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w3 (PetersenWireProjection.cons pc0w0 rfl))))))))) (by decide +kernel)
theorem b4_2941 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2941 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(2,true))] s4_2941 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xfafafafa,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w15 (PetersenWireProjection.cons pc2w12 rfl))))))))) (by decide +kernel)
theorem b4_2942 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2942 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(5,false),(0,false)),(false,(0,true),(4,true))] s4_2942 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons pc26w23 rfl))))))))) (by decide +kernel)
theorem b4_2943 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2943 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(0,true)),(false,(4,false),(0,false)),(false,(0,true),(7,true))] s4_2943 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff55005500ffffffff55005500,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons pc30w35 rfl))))))))) (by decide +kernel)
theorem b4_2944 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2944 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2944 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w50 (PetersenWireProjection.cons pc41w47 rfl))))))))) (by decide +kernel)
theorem b4_2945 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2945 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,true),(1,true)),(false,(1,true),(4,true))] s4_2945 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons pc26w58 rfl))))))))) (by decide +kernel)
theorem b4_2946 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2946 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(6,true),(3,true)),(false,(1,true),(7,true))] s4_2946 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff55005500ffffffff55005500,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons pc30w60 rfl))))))))) (by decide +kernel)
theorem b4_2947 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2947 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2947 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w67 (PetersenWireProjection.cons pc37w62 rfl))))))))) (by decide +kernel)
theorem b4_2948 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2948 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2948 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w75 (PetersenWireProjection.cons pc37w74 rfl))))))))) (by decide +kernel)
theorem b4_2949 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2949 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(5,true),(3,true)),(false,(1,true),(0,false))] s4_2949 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff5f5fffff5f5fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons pc26w77 rfl))))))))) (by decide +kernel)
theorem b4_2950 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2950 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(7,true),(3,true)),(false,(1,true),(0,false))] s4_2950 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff5f5f0f0f5f5f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons pc26w81 rfl))))))))) (by decide +kernel)
theorem b4_2951 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2951 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false)),(false,(3,true),(5,true)),(false,(1,true),(0,false))] s4_2951 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffafafffffafafffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons pc26w84 rfl))))))))) (by decide +kernel)
theorem b4_2952 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2952 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(7,true),(3,true)),(false,(1,true),(0,false))] s4_2952 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons pc26w86 rfl))))))))) (by decide +kernel)
theorem b4_2953 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2953 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,false),(7,false)),(false,(0,true),(1,false))] s4_2953 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w80 (PetersenWireProjection.cons pc26w88 rfl))))))))) (by decide +kernel)
theorem b4_2954 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2954 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(5,false),(0,false)),(false,(0,true),(4,true))] s4_2954 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fffff0f0fffff0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w90 (PetersenWireProjection.cons pc26w82 rfl))))))))) (by decide +kernel)
theorem b4_2955 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2955 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,true),(5,true)),(false,(1,true),(4,true))] s4_2955 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fafafafafafafafa,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons pc26w78 rfl))))))))) (by decide +kernel)
theorem b4_2956 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2956 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(6,true)),(false,(1,false),(0,false)),(false,(0,true),(4,true))] s4_2956 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0fafafafafafafafa,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons pc26w82 rfl))))))))) (by decide +kernel)
theorem b4_2957 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2957 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,false),(7,false)),(false,(0,true),(4,true))] s4_2957 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0fffff0f0fffff0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w93 (PetersenWireProjection.cons pc26w78 rfl))))))))) (by decide +kernel)
theorem b4_2958 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2958 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(0,false),(1,false)),(false,(0,true),(4,true))] s4_2958 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0fafaf0f0fafaf0f0fafaf0f0fafa,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w95 (PetersenWireProjection.cons pc26w78 rfl))))))))) (by decide +kernel)
theorem b4_2959 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2959 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2959 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w97 rfl)))))))) (by decide +kernel)
theorem b4_2960 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2960 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2960 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w102 (PetersenWireProjection.cons pc2w100 rfl))))))))) (by decide +kernel)
theorem b4_2961 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2961 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2961 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w97 (PetersenWireProjection.cons pc0w104 rfl))))))))) (by decide +kernel)
theorem b4_2962 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2962 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,true))] s4_2962 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffccffcc] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w97 (PetersenWireProjection.cons pc0w0 rfl))))))))) (by decide +kernel)
theorem b4_2963 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2963 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s4_2963 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w97 (PetersenWireProjection.cons pc0w106 rfl))))))))) (by decide +kernel)
theorem b4_2964 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2964 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2964 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w107 (PetersenWireProjection.cons pc41w47 rfl))))))))) (by decide +kernel)
theorem b4_2965 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2965 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,false)),(false,(3,true),(1,true)),(false,(1,true),(4,true))] s4_2965 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w109 (PetersenWireProjection.cons pc26w58 rfl))))))))) (by decide +kernel)
theorem b4_2966 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2966 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(3,false)),(false,(6,true),(3,true)),(false,(1,true),(7,true))] s4_2966 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffaa00aa00ffffffffaa00aa00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons pc30w60 rfl))))))))) (by decide +kernel)
theorem b4_2967 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2967 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,false)),(false,(3,true),(5,true)),(false,(1,true),(4,true))] s4_2967 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xfafafafafafafafaf0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w118 (PetersenWireProjection.cons pc32w113 rfl))))))))) (by decide +kernel)
theorem b4_2968 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2968 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2968 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w104 rfl)))))))) (by decide +kernel)
theorem b4_2969 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2969 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s4_2969 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffccffcc] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w104 (PetersenWireProjection.cons pc0w0 rfl))))))))) (by decide +kernel)
theorem b4_2970 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2970 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2970 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w126 (PetersenWireProjection.cons pc41w125 rfl))))))))) (by decide +kernel)
theorem b4_2971 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2971 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(3,true),(7,true)),(false,(1,true),(4,true))] s4_2971 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w128 (PetersenWireProjection.cons pc26w23 rfl))))))))) (by decide +kernel)
theorem b4_2972 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2972 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2972 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w126 (PetersenWireProjection.cons pc41w129 rfl))))))))) (by decide +kernel)
theorem b4_2973 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2973 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s4_2973 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w135 (PetersenWireProjection.cons pc3w130 rfl))))))))) (by decide +kernel)
theorem b4_2974 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2974 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true)),(false,(8,true),(0,false))] s4_2974 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xfffffffffffffffffafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w128 (PetersenWireProjection.cons pc26w142 rfl))))))))) (by decide +kernel)
theorem b4_2975 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2975 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(6,true),(1,true)),(false,(1,true),(7,true))] s4_2975 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff000f000fffffffff000f000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w143 (PetersenWireProjection.cons pc30w35 rfl))))))))) (by decide +kernel)
theorem b4_2976 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2976 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(0,true),(6,true)),(false,(2,true),(0,false))] s4_2976 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff000f000fffffffff000f000,0xfffffffffaaafaaafffffffffaaafaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w143 (PetersenWireProjection.cons pc30w145 rfl))))))))) (by decide +kernel)
theorem b4_2977 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2977 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(0,true)),(false,(6,true),(4,true)),(false,(1,true),(7,true))] s4_2977 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff50505050ffffffff50505050] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons pc30w146 rfl))))))))) (by decide +kernel)
theorem b4_2978 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2978 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(0,false),(1,false)),(false,(0,true),(7,true))] s4_2978 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00aa00aaffffffff00aa00aa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons pc30w150 rfl))))))))) (by decide +kernel)
theorem b4_2979 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2979 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(0,false),(3,false)),(false,(0,true),(7,true))] s4_2979 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00f000f0ffffffff00f000f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons pc30w152 rfl))))))))) (by decide +kernel)
theorem b4_2980 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2980 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,false)),(false,(3,true),(5,true)),(false,(1,true),(4,true))] s4_2980 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafaf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w78 (PetersenWireProjection.cons pc26w154 rfl))))))))) (by decide +kernel)
theorem b4_2981 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2981 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,false)),(false,(6,true),(4,true)),(false,(1,true),(7,true))] s4_2981 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffffa0a0a0a0ffffffffa0a0a0a0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w149 (PetersenWireProjection.cons pc30w155 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
