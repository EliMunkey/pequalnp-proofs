import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc0w5 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xcc00cc00 := PetersenWireProjection.derive 0 stored49 stored55 rfl rfl

private theorem pc0w4 : PetersenPackedPin.project cycle0 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xcc00cc00 := PetersenWireProjection.derive 3 pc0w5 stored53 rfl rfl

private theorem pc0w10 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w9 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w10 stored50 rfl rfl

private theorem pc0w13 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored53 rfl rfl
private theorem pc0w14 : PetersenPackedPin.project cycle0 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored53 rfl rfl
private theorem pc0w12 : PetersenPackedPin.project cycle0 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 pc0w13 pc0w14 rfl rfl







private theorem pc2w23 : PetersenPackedPin.project cycle2 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 stored41 stored42 rfl rfl
private theorem pc2w24 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w22 : PetersenPackedPin.project cycle2 (0xcccccccc000000000000000000000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w23 pc2w24 rfl rfl

private theorem pc0w27 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xff00 := PetersenWireProjection.derive 1 stored49 stored51 rfl rfl
private theorem pc0w28 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w26 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w27 pc0w28 rfl rfl
private theorem pc0w30 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w29 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 3 pc0w9 pc0w30 rfl rfl
private theorem pc0w32 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w31 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 3 pc0w9 pc0w32 rfl rfl
private theorem pc2w34 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc2w33 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w34 pc2w24 rfl rfl
private theorem pc2w36 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w35 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0 := PetersenWireProjection.derive 3 pc2w36 stored41 rfl rfl
private theorem pc2w39 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored41 stored44 rfl rfl
private theorem pc2w40 : PetersenPackedPin.project cycle2 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored42 stored44 rfl rfl
private theorem pc2w38 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f0 := PetersenWireProjection.derive 3 pc2w39 pc2w40 rfl rfl
private theorem pc2w37 : PetersenPackedPin.project cycle2 (0xccccffff0000ffffccccffff0000ffffccccffff0000ffffcccccccc00000000 : BitVec 256) = 0xff00f0 := PetersenWireProjection.derive 3 pc2w38 pc2w24 rfl rfl
private theorem pc2w41 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w43 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored45 rfl rfl
private theorem pc2w44 : PetersenPackedPin.project cycle2 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored42 stored45 rfl rfl
private theorem pc2w42 : PetersenPackedPin.project cycle2 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 pc2w43 pc2w44 rfl rfl
private theorem pc2w45 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w24 stored41 rfl rfl




private theorem pc3w48 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl


private theorem pc3w53 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored33 stored37 rfl rfl
private theorem pc3w55 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored34 stored37 rfl rfl
private theorem pc3w52 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 1 pc3w53 pc3w55 rfl rfl

private theorem pc3w57 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc2w59 : PetersenPackedPin.project cycle2 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc2w24 stored44 rfl rfl
private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored37 stored39 rfl rfl
private theorem pc3w61 : PetersenPackedPin.project cycle3 (0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc : BitVec 256) = 0xeeeeeeee := PetersenWireProjection.derive 3 pc3w62 stored35 rfl rfl
private theorem pc3w60 : PetersenPackedPin.project cycle3 (0xffffffffffccffccffffffffffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xeaeaeaea := PetersenWireProjection.derive 0 pc3w61 pc3w53 rfl rfl
private theorem pc3w64 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored38 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored38 rfl rfl
private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w64 pc3w65 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored38 stored39 rfl rfl
private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w68 stored35 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0fffffffffcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w67 pc3w65 rfl rfl
private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w71 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w69 : PetersenPackedPin.project cycle3 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 pc3w70 pc3w71 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0x30303030 := PetersenWireProjection.derive 1 pc3w73 pc3w71 rfl rfl
private theorem pc3w76 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w75 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w76 stored33 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w75 pc3w57 rfl rfl
private theorem pc3w78 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w78 stored33 rfl rfl
private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w78 stored33 rfl rfl
private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w80 pc3w57 rfl rfl




private theorem pc37w83 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl
private theorem pc37w87 : PetersenPackedPin.project extra37 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored67 stored66 rfl rfl
private theorem pc37w88 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl
private theorem pc37w86 : PetersenPackedPin.project extra37 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc37w87 pc37w88 rfl rfl



private theorem pc37w94 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored65 stored71 rfl rfl
private theorem pc37w93 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 1 pc37w94 stored67 rfl rfl
private theorem pc37w95 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 0 stored66 stored71 rfl rfl
private theorem pc37w92 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 pc37w93 pc37w95 rfl rfl








private theorem pc1w105 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w106 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w104 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w105 pc1w106 rfl rfl

private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w109 stored33 rfl rfl
private theorem pc3w111 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w111 pc3w57 rfl rfl
private theorem pc3w112 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w78 stored35 rfl rfl
private theorem pc3w113 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w78 stored36 rfl rfl
private theorem pc3w114 : PetersenPackedPin.project cycle3 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w109 stored37 rfl rfl
private theorem pc3w115 : PetersenPackedPin.project cycle3 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w78 stored37 rfl rfl
private theorem pc3w116 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w78 stored38 rfl rfl



private theorem pc73w120 : PetersenPackedPin.project extra73 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x4444444444444444 := PetersenWireProjection.derive 1 stored129 stored131 rfl rfl
private theorem pc73w122 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored130 stored131 rfl rfl
private theorem pc73w119 : PetersenPackedPin.project extra73 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 pc73w120 pc73w122 rfl rfl




private theorem pc73w129 : PetersenPackedPin.project extra73 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored130 stored131 rfl rfl
private theorem pc73w128 : PetersenPackedPin.project extra73 (0xffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w129 stored129 rfl rfl
private theorem pc73w130 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored131 stored135 rfl rfl
private theorem pc73w127 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000ccccccccffffffffcccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w128 pc73w130 rfl rfl

private theorem pc73w134 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w135 : PetersenPackedPin.project extra73 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored131 stored135 rfl rfl
private theorem pc73w133 : PetersenPackedPin.project extra73 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w134 pc73w135 rfl rfl
private theorem pc73w132 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000ccccccccffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w133 pc73w120 rfl rfl
private theorem pc2w138 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w137 : PetersenPackedPin.project cycle2 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w138 stored43 rfl rfl
private theorem pc2w139 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w136 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc2w137 pc2w139 rfl rfl
private theorem pc1w141 : PetersenPackedPin.project cycle1 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored63 rfl rfl
private theorem pc1w140 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc1w141 stored59 rfl rfl
private theorem pc2w143 : PetersenPackedPin.project cycle2 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored43 stored47 rfl rfl
private theorem pc2w142 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffff33333333000000003333333300000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w143 stored41 rfl rfl
private theorem pc2w144 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w139 stored43 rfl rfl
private theorem pc2w146 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored42 stored43 rfl rfl
private theorem pc2w145 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc2w146 stored41 rfl rfl
private theorem pc2w148 : PetersenPackedPin.project cycle2 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored43 stored44 rfl rfl
private theorem pc2w147 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 2 pc2w40 pc2w148 rfl rfl
private theorem pc2w149 : PetersenPackedPin.project cycle2 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc2w143 stored46 rfl rfl
theorem b4_2604 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2604 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(1,false))] s4_2604 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0xcc00cc00,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons pc0w4 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2605 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2605 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s4_2605 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w12 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2606 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2606 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2606 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w22 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2607 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2607 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2607 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2608 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2608 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s4_2608 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcc00cc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w29 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2609 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2609 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s4_2609 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xff0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w31 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2610 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2610 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2610 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w33 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2611 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2611 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false)),(false,(0,true),(3,true))] s4_2611 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xfafaf0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w33 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w35 rfl))))))))) (by decide +kernel)
theorem b4_2612 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2612 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_2612 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xff00f0,0xcccccccc,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w37 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2613 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2613 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2613 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2614 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2614 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2614 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w41 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2615 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2615 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,false),(4,true))] s4_2615 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w42 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2616 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2616 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,false),(4,true))] s4_2616 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w42 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w45 rfl))))))))) (by decide +kernel)
theorem b4_2617 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2617 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2617 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w52 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2618 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2618 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,false),(4,true))] s4_2618 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0xf0f0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w24 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w42 (PetersenWireProjection.cons pc2w59 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2619 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2619 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false)),(false,(0,true),(1,true))] s4_2619 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xff00ff00,0xcccccccc,0xeaeaeaea,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons pc3w60 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2620 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2620 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2620 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2621 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2621 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_2621 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2622 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2622 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,false))] s4_2622 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x33330000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2623 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2623 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,false))] s4_2623 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x30303030,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w57 (PetersenWireProjection.cons pc3w72 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2624 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2624 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2624 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2625 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2625 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2625 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w77 rfl))))))))) (by decide +kernel)
theorem b4_2626 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2626 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2626 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w79 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2627 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2627 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2627 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w79 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w48 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2628 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2628 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2628 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons pc37w92 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons pc37w86 (PetersenWireProjection.cons pc37w83 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 rfl))))))))) (by decide +kernel)
theorem b4_2629 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2629 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2629 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w104 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2630 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2630 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2630 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w108 rfl))))))))) (by decide +kernel)
theorem b4_2631 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2631 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2631 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w77 rfl))))))))) (by decide +kernel)
theorem b4_2632 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2632 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2632 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w112 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2633 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2633 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2633 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w113 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2634 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2634 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2634 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w114 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2635 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2635 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2635 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w115 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2636 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2636 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2636 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w116 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2637 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2637 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2637 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w127 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons pc73w119 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2638 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2638 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2638 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w132 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2639 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2639 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2639 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w136 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2640 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2640 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2640 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xffff0000,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w140 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2641 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2641 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2641 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w144 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w142 rfl))))))))) (by decide +kernel)
theorem b4_2642 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2642 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2642 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w144 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w145 rfl))))))))) (by decide +kernel)
theorem b4_2643 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2643 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2643 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w144 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w147 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2644 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2644 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2644 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w144 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w149 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2645 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2645 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2645 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w144 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w149 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))) (by decide +kernel)
end Orbits1020Cost12
