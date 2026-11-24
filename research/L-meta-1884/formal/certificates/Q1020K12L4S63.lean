import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc2w3 : PetersenPackedPin.project cycle2 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored42 stored46 rfl rfl

private theorem pc2w5 : PetersenPackedPin.project cycle2 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored43 stored46 rfl rfl
private theorem pc2w2 : PetersenPackedPin.project cycle2 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc2w3 pc2w5 rfl rfl



private theorem pc2w11 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w10 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w11 stored43 rfl rfl



private theorem pc0w13 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl





private theorem pc0w22 : PetersenPackedPin.project cycle0 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored49 stored50 rfl rfl
private theorem pc0w23 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w21 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 3 pc0w22 pc0w23 rfl rfl




private theorem pc30w26 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl




private theorem pc30w34 : PetersenPackedPin.project extra30 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 2 stored8 stored9 rfl rfl
private theorem pc30w35 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w33 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xaa00aa00faf0faf0aa00aa00faf0faf0 := PetersenWireProjection.derive 3 pc30w34 pc30w35 rfl rfl





private theorem pc3w39 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl



private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 stored33 stored34 rfl rfl
private theorem pc3w47 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 3 pc3w46 pc3w47 rfl rfl




private theorem pc73w52 : PetersenPackedPin.project extra73 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored130 stored135 rfl rfl

private theorem pc73w51 : PetersenPackedPin.project extra73 (0xffffffff33333333ffffffff00000000ffffffff33333333ffffffff00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc73w52 stored131 rfl rfl



private theorem pc73w60 : PetersenPackedPin.project extra73 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored131 stored135 rfl rfl
private theorem pc73w59 : PetersenPackedPin.project extra73 (0x33333333000000000000000000000000333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w60 stored130 rfl rfl
private theorem pc73w61 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored131 stored135 rfl rfl
private theorem pc73w58 : PetersenPackedPin.project extra73 (0xcccccccc33333333cccccccc00000000cccccccc33333333cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w59 pc73w61 rfl rfl

private theorem pc73w64 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w65 : PetersenPackedPin.project extra73 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored131 stored135 rfl rfl
private theorem pc73w63 : PetersenPackedPin.project extra73 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w64 pc73w65 rfl rfl
private theorem pc0w67 : PetersenPackedPin.project cycle0 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfff0fff0 := PetersenWireProjection.derive 3 stored49 stored54 rfl rfl
private theorem pc0w68 : PetersenPackedPin.project cycle0 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored51 stored54 rfl rfl
private theorem pc0w66 : PetersenPackedPin.project cycle0 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfff0f0f0 := PetersenWireProjection.derive 0 pc0w67 pc0w68 rfl rfl
private theorem pc0w71 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xcc00cc00 := PetersenWireProjection.derive 0 stored49 stored55 rfl rfl
private theorem pc0w72 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl
private theorem pc0w70 : PetersenPackedPin.project cycle0 (0xcccccccc00000000000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w71 pc0w72 rfl rfl
private theorem pc0w74 : PetersenPackedPin.project cycle0 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored54 stored55 rfl rfl
private theorem pc0w73 : PetersenPackedPin.project cycle0 (0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w74 stored50 rfl rfl
private theorem pc0w69 : PetersenPackedPin.project cycle0 (0xccccccccc0c0c0c00000000000000000c0c0c0c0c0c0c0c00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w70 pc0w73 rfl rfl



private theorem pc1w78 : PetersenPackedPin.project cycle1 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored58 stored62 rfl rfl

private theorem pc1w80 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored62 rfl rfl
private theorem pc1w77 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 pc1w78 pc1w80 rfl rfl



private theorem pc1w86 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w85 : PetersenPackedPin.project cycle1 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w77 pc1w86 rfl rfl

private theorem pc3w89 : PetersenPackedPin.project cycle3 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored38 rfl rfl
private theorem pc3w90 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored38 rfl rfl
private theorem pc3w88 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w89 pc3w90 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w47 stored34 rfl rfl
private theorem pc3w93 : PetersenPackedPin.project cycle3 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored38 stored39 rfl rfl
private theorem pc3w91 : PetersenPackedPin.project cycle3 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c0ccccccccc0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w92 pc3w93 rfl rfl
private theorem pc3w95 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored34 stored35 rfl rfl
private theorem pc3w96 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored38 stored39 rfl rfl
private theorem pc3w94 : PetersenPackedPin.project cycle3 (0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 3 pc3w95 pc3w96 rfl rfl



private theorem pc18w100 : PetersenPackedPin.project tree18 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored186 stored188 rfl rfl


private theorem pc18w102 : PetersenPackedPin.project tree18 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 stored187 stored191 rfl rfl
private theorem pc18w99 : PetersenPackedPin.project tree18 (0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc18w100 pc18w102 rfl rfl
private theorem pc18w106 : PetersenPackedPin.project tree18 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored186 stored187 rfl rfl
private theorem pc18w107 : PetersenPackedPin.project tree18 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored188 stored187 rfl rfl
private theorem pc18w105 : PetersenPackedPin.project tree18 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w106 pc18w107 rfl rfl


private theorem pc18w112 : PetersenPackedPin.project tree18 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000 := PetersenWireProjection.derive 0 stored188 stored191 rfl rfl
private theorem pc18w111 : PetersenPackedPin.project tree18 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w112 stored186 rfl rfl
private theorem pc18w113 : PetersenPackedPin.project tree18 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored187 stored191 rfl rfl
private theorem pc18w110 : PetersenPackedPin.project tree18 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c0ccccccccc0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc18w111 pc18w113 rfl rfl

private theorem pc3w116 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w115 : PetersenPackedPin.project cycle3 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c0cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w91 pc3w116 rfl rfl
private theorem pc18w118 : PetersenPackedPin.project tree18 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f0 := PetersenWireProjection.derive 1 stored185 stored191 rfl rfl
private theorem pc18w117 : PetersenPackedPin.project tree18 (0xccccccccc0c0c0c0c0c0c0c0c0c0c0c0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc18w105 pc18w118 rfl rfl
private theorem pc3w120 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored38 rfl rfl
private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w120 pc3w89 rfl rfl
private theorem pc3w122 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0 : BitVec 256) = 0xcfcfcccc := PetersenWireProjection.derive 3 pc3w46 pc3w90 rfl rfl
private theorem pc3w121 : PetersenPackedPin.project cycle3 (0xccccccccc0c0c0c0ccccccccc0c0c0c0ccccccccccccccccccccccccc0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w122 stored39 rfl rfl
private theorem pc1w124 : PetersenPackedPin.project cycle1 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored62 rfl rfl
private theorem pc1w123 : PetersenPackedPin.project cycle1 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w124 pc1w80 rfl rfl
private theorem pc1w126 : PetersenPackedPin.project cycle1 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x30303030 := PetersenWireProjection.derive 1 stored58 stored63 rfl rfl
private theorem pc1w125 : PetersenPackedPin.project cycle1 (0xccccccccc0c0c0c0fffffffff0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc1w123 pc1w126 rfl rfl
private theorem pc3w128 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored33 stored37 rfl rfl
private theorem pc3w129 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored34 stored37 rfl rfl
private theorem pc3w127 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 1 pc3w128 pc3w129 rfl rfl
private theorem pc3w132 : PetersenPackedPin.project cycle3 (0xffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w47 stored37 rfl rfl
private theorem pc3w133 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 stored33 stored34 rfl rfl
private theorem pc3w131 : PetersenPackedPin.project cycle3 (0xffccffccff00ff00ffffffffffffffffffccffccff00ff00ffccffccff00ff00 : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 3 pc3w132 pc3w133 rfl rfl
private theorem pc3w130 : PetersenPackedPin.project cycle3 (0xcccccccccc00cc00cccccccccccccccccccccccccc00cc00cccccccccc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w131 stored39 rfl rfl
private theorem pc2w135 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored45 rfl rfl
private theorem pc2w136 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored43 stored45 rfl rfl
private theorem pc2w134 : PetersenPackedPin.project cycle2 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w135 pc2w136 rfl rfl
private theorem pc2w138 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w137 : PetersenPackedPin.project cycle2 (0xcccccccccc00cc00ffffffffff00ff00cc00cc00cc00cc00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc2w134 pc2w138 rfl rfl
private theorem pc1w140 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w139 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w140 stored60 rfl rfl
private theorem pc1w143 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w144 : PetersenPackedPin.project cycle1 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored60 stored63 rfl rfl
private theorem pc1w142 : PetersenPackedPin.project cycle1 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 3 pc1w143 pc1w144 rfl rfl
private theorem pc1w141 : PetersenPackedPin.project cycle1 (0xcccccccccccc0000cccccccccccc0000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w142 pc1w140 rfl rfl
private theorem pc3w145 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w47 stored36 rfl rfl
private theorem pc3w148 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored36 stored39 rfl rfl
private theorem pc3w147 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w47 pc3w148 rfl rfl
private theorem pc3w146 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccc0000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w147 pc3w116 rfl rfl
private theorem pc3w150 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w149 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccccccccccccccccccc0000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w147 pc3w150 rfl rfl
private theorem pc0w152 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc0w153 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w151 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w152 pc0w153 rfl rfl
private theorem pc0w155 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w156 : PetersenPackedPin.project cycle0 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored55 rfl rfl
private theorem pc0w154 : PetersenPackedPin.project cycle0 (0xffffffff33333333ffffffff0000000033333333333333330000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w155 pc0w156 rfl rfl
private theorem pc0w157 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w158 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w155 stored50 rfl rfl
private theorem pc0w159 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w153 stored49 rfl rfl
private theorem pc3w161 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored33 stored35 rfl rfl
private theorem pc3w162 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w160 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffc0c0 := PetersenWireProjection.derive 3 pc3w161 pc3w162 rfl rfl
private theorem pc3w163 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w166 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w165 : PetersenPackedPin.project cycle3 (0x333333330000000000000000000000003333333300000000 : BitVec 256) = 0xcccc := PetersenWireProjection.derive 1 pc3w166 stored34 rfl rfl
private theorem pc3w164 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff3333ffff0000ffff0000ffff0000ffff3333ffff0000 : BitVec 256) = 0xff00ffcc := PetersenWireProjection.derive 3 pc3w165 stored36 rfl rfl
private theorem pc0w168 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w169 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored52 rfl rfl
private theorem pc0w167 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc0w168 pc0w169 rfl rfl
private theorem pc0w170 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w153 stored52 rfl rfl
private theorem pc0w172 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored52 rfl rfl
private theorem pc0w171 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 pc0w172 pc0w169 rfl rfl
private theorem pc3w174 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xfff0fff0 := PetersenWireProjection.derive 3 stored33 stored36 rfl rfl
private theorem pc3w175 : PetersenPackedPin.project cycle3 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored35 stored36 rfl rfl
private theorem pc3w173 : PetersenPackedPin.project cycle3 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffc0ffc0 := PetersenWireProjection.derive 0 pc3w174 pc3w175 rfl rfl
private theorem pc0w176 : PetersenPackedPin.project cycle0 (0xffffffffffffccccffffffffffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w170 pc0w155 rfl rfl
private theorem pc0w177 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w153 stored51 rfl rfl
private theorem pc1w178 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl
private theorem pc1w180 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl
private theorem pc1w181 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w179 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w180 pc1w181 rfl rfl
private theorem pc1w182 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc0w183 : PetersenPackedPin.project cycle0 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w153 stored53 rfl rfl
private theorem pc3w185 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w166 stored38 rfl rfl
private theorem pc3w186 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored38 rfl rfl
private theorem pc3w184 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0f0f0f0f0f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccc := PetersenWireProjection.derive 1 pc3w185 pc3w186 rfl rfl
private theorem pc0w187 : PetersenPackedPin.project cycle0 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc0w153 stored54 rfl rfl
theorem b4_2646 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2646 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2646 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0x0,0xff00ff00,0x0,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w10 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w2 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2647 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2647 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(1,false))] s4_2647 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w21 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w13 rfl))))))))) (by decide +kernel)
theorem b4_2648 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2648 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(1,false),(4,false)),(false,(1,true),(0,true))] s4_2648 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00faf0faf0aa00aa00faf0faf0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w33 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w26 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2649 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2649 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2649 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0000,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w39 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2650 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2650 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2650 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w58 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons pc73w51 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2651 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2651 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2651 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w58 (PetersenWireProjection.cons pc73w63 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2652 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2652 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false)),(false,(3,true),(0,true))] s4_2652 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0x0,0x0,0xffff0000,0xfff0f0f0,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w69 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w66 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2653 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2653 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(4,false))] s4_2653 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xff00ff00,0x0,0xffff0000,0xf0f00000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w85 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w77 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2654 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2654 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(1,false))] s4_2654 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w91 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w88 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2655 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2655 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(1,false))] s4_2655 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w91 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w94 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2656 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2656 := by
  intro m le c
  apply rejects_sound tree18 i6 6 tgt small18 hot18 [] s4_2656 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0xffff0000ffff0000,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored192 (PetersenWireProjection.cons pc18w110 (PetersenWireProjection.cons stored190 (PetersenWireProjection.cons stored189 (PetersenWireProjection.cons stored188 (PetersenWireProjection.cons pc18w105 (PetersenWireProjection.cons pc18w99 (PetersenWireProjection.cons stored186 (PetersenWireProjection.cons stored185 rfl))))))))) (by decide +kernel)
theorem b4_2657 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2657 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_2657 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w115 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w88 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2658 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2658 := by
  intro m le c
  apply rejects_sound tree18 i6 6 tgt small18 hot18 [] s4_2658 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored192 (PetersenWireProjection.cons pc18w117 (PetersenWireProjection.cons stored191 (PetersenWireProjection.cons stored190 (PetersenWireProjection.cons stored189 (PetersenWireProjection.cons stored188 (PetersenWireProjection.cons pc18w105 (PetersenWireProjection.cons stored186 (PetersenWireProjection.cons stored185 rfl))))))))) (by decide +kernel)
theorem b4_2659 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2659 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2659 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w121 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w119 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2660 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2660 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2660 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xff00ff00,0x0,0xffff0000,0x0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w125 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons pc1w123 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2661 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2661 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2661 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w130 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2662 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2662 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2662 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w137 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w134 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2663 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2663 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2663 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w141 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w139 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2664 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2664 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2664 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w146 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w145 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2665 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2665 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2665 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w149 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w145 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2666 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2666 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2666 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w151 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2667 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2667 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s4_2667 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2668 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2668 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2668 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2669 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2669 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2669 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w157 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2670 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2670 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s4_2670 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w158 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2671 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2671 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2671 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w158 (PetersenWireProjection.cons pc0w159 rfl))))))))) (by decide +kernel)
theorem b4_2672 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2672 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false)),(false,(0,true),(5,true))] s4_2672 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w160 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2673 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2673 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true)),(false,(0,true),(4,true))] s4_2673 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ffcc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w164 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2674 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2674 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2674 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w167 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2675 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2675 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2675 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xffff0000,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w167 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w157 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2676 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2676 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2676 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w170 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w158 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2677 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2677 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2677 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w171 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2678 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2678 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2678 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w171 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w159 rfl))))))))) (by decide +kernel)
theorem b4_2679 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2679 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false)),(false,(4,true),(0,true))] s4_2679 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffc0ffc0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w173 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2680 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2680 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2680 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w176 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2681 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2681 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2681 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w177 (PetersenWireProjection.cons pc0w171 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2682 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2682 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(1,false))] s4_2682 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f0f0f0,0x0,0xffff0000] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w182 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w179 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w178 rfl))))))))) (by decide +kernel)
theorem b4_2683 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2683 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2683 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons pc0w183 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w171 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2684 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2684 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true))] s4_2684 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w184 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2685 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2685 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2685 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w163 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w185 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w162 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2686 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2686 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2686 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w187 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w158 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2687 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2687 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2687 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w153 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w187 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w171 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
