import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0





private theorem pc30w7 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl


private theorem pc30w8 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored11 stored13 rfl rfl
private theorem pc30w6 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w7 pc30w8 rfl rfl
private theorem pc30w11 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl
private theorem pc30w5 : PetersenPackedPin.project extra30 (0xc0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w6 pc30w11 rfl rfl

private theorem pc30w14 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w15 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w14 pc30w15 rfl rfl







private theorem pc32w24 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w26 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w23 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc32w24 pc32w26 rfl rfl
private theorem pc32w27 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl
private theorem pc32w22 : PetersenPackedPin.project extra32 (0xcc000000cc000000cc000000cc000000cc000000cc000000cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc32w23 pc32w27 rfl rfl

private theorem pc32w30 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc32w29 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w30 pc32w27 rfl rfl
private theorem pc32w33 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored25 stored28 rfl rfl
private theorem pc32w32 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc32w33 stored24 rfl rfl
private theorem pc32w31 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w32 pc32w27 rfl rfl
private theorem pc32w35 : PetersenPackedPin.project extra32 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 1 stored26 stored29 rfl rfl
private theorem pc32w34 : PetersenPackedPin.project extra32 (0xcc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00cc00cc00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc32w35 stored28 rfl rfl
private theorem pc32w38 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored27 stored28 rfl rfl
private theorem pc32w37 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc32w30 pc32w38 rfl rfl
private theorem pc32w36 : PetersenPackedPin.project extra32 (0xcc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w37 pc32w27 rfl rfl






private theorem pc2w47 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl

private theorem pc2w48 : PetersenPackedPin.project cycle2 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0xaa00aa00 := PetersenWireProjection.derive 0 stored44 stored47 rfl rfl
private theorem pc2w46 : PetersenPackedPin.project cycle2 (0xcccc0000cccc0000cccc0000cccc0000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xaa0aaa0a := PetersenWireProjection.derive 3 pc2w47 pc2w48 rfl rfl
private theorem pc2w51 : PetersenPackedPin.project cycle2 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored42 stored44 rfl rfl
private theorem pc2w50 : PetersenPackedPin.project cycle2 (0xffff000000000000ffffffff00000000ffff000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w51 stored43 rfl rfl
private theorem pc2w45 : PetersenPackedPin.project cycle2 (0xcccc000000000000cccc000000000000cccc000000000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w46 pc2w50 rfl rfl

private theorem pc2w54 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored41 stored44 rfl rfl
private theorem pc2w53 : PetersenPackedPin.project cycle2 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f0 := PetersenWireProjection.derive 3 pc2w54 pc2w51 rfl rfl







private theorem pc34w62 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xcccc0000cccc00000000000000000000cccc0000cccc00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w62 stored17 rfl rfl

private theorem pc34w66 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w67 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w65 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w66 pc34w67 rfl rfl
private theorem pc34w68 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w62 stored16 rfl rfl
private theorem pc34w70 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w69 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc34w70 pc34w62 rfl rfl






private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w76 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w77 pc3w79 rfl rfl
private theorem pc3w82 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w81 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w82 stored33 rfl rfl

private theorem pc3w83 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored36 stored39 rfl rfl
private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w81 pc3w83 rfl rfl

private theorem pc3w87 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f0 := PetersenWireProjection.derive 1 stored33 stored36 rfl rfl
private theorem pc3w88 : PetersenPackedPin.project cycle3 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored34 stored36 rfl rfl
private theorem pc3w86 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f0 := PetersenWireProjection.derive 3 pc3w87 pc3w88 rfl rfl
private theorem pc3w91 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 stored35 stored36 rfl rfl
private theorem pc3w90 : PetersenPackedPin.project cycle3 (0xffff000000000000ffff000000000000ffff000000000000000000000000 : BitVec 256) = 0xcc00c0 := PetersenWireProjection.derive 0 pc3w91 pc3w92 rfl rfl
private theorem pc3w89 : PetersenPackedPin.project cycle3 (0xcccc0000cccccccccccc0000cccccccccccc0000cccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc3w90 stored39 rfl rfl






private theorem pc0w100 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w99 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w100 stored50 rfl rfl


private theorem pc0w103 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w105 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w102 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w103 pc0w105 rfl rfl
private theorem pc2w107 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc2w108 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w106 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w107 pc2w108 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w111 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w81 pc3w110 rfl rfl
private theorem pc3w114 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored36 stored39 rfl rfl
private theorem pc3w113 : PetersenPackedPin.project cycle3 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w91 pc3w114 rfl rfl
private theorem pc3w112 : PetersenPackedPin.project cycle3 (0xcccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w113 pc3w110 rfl rfl
private theorem pc3w116 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w110 pc3w83 rfl rfl
private theorem pc3w115 : PetersenPackedPin.project cycle3 (0xcccccccccccc0000cccccccccccc0000cccccccccccc0000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w81 pc3w116 rfl rfl
private theorem pc0w117 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w118 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w119 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc0w121 : PetersenPackedPin.project cycle0 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33003300 := PetersenWireProjection.derive 1 stored49 stored55 rfl rfl
private theorem pc0w120 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000ffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w121 stored50 rfl rfl
private theorem pc3w123 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w122 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc00000000cccccccccccccccccccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w79 pc3w123 rfl rfl
private theorem pc3w124 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w79 pc3w110 rfl rfl






private theorem pc1w131 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl


private theorem pc1w134 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w136 : PetersenPackedPin.project cycle1 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored58 stored60 rfl rfl
private theorem pc1w133 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w134 pc1w136 rfl rfl
private theorem pc1w137 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc3w138 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w77 pc3w123 rfl rfl
private theorem pc3w139 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w77 pc3w110 rfl rfl
private theorem pc3w140 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w79 stored33 rfl rfl
private theorem pc3w141 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc3w143 : PetersenPackedPin.project cycle3 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w79 stored37 rfl rfl
private theorem pc3w142 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w143 pc3w77 rfl rfl






private theorem pc107w151 : PetersenPackedPin.project extra107 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored166 rfl rfl
private theorem pc107w150 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w151 stored161 rfl rfl

private theorem pc107w153 : PetersenPackedPin.project extra107 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored167 stored166 rfl rfl
private theorem pc107w149 : PetersenPackedPin.project extra107 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w150 pc107w153 rfl rfl
private theorem pc107w156 : PetersenPackedPin.project extra107 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000 := PetersenWireProjection.derive 0 stored161 stored166 rfl rfl
private theorem pc107w157 : PetersenPackedPin.project extra107 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 0 stored162 stored166 rfl rfl
private theorem pc107w155 : PetersenPackedPin.project extra107 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc107w156 pc107w157 rfl rfl

private theorem pc107w160 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored161 stored167 rfl rfl
private theorem pc107w161 : PetersenPackedPin.project extra107 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored162 stored167 rfl rfl
private theorem pc107w159 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w160 pc107w161 rfl rfl



private theorem pc39w163 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl



private theorem pc39w170 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored73 stored79 rfl rfl
private theorem pc39w171 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 0 stored74 stored79 rfl rfl
private theorem pc39w169 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 pc39w170 pc39w171 rfl rfl


private theorem pc39w174 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w176 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored74 stored76 rfl rfl
private theorem pc39w173 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w174 pc39w176 rfl rfl


private theorem pc41w177 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl




private theorem pc41w185 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 0 stored91 stored95 rfl rfl
private theorem pc41w186 : PetersenPackedPin.project extra41 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored89 stored95 rfl rfl
private theorem pc41w184 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 pc41w185 pc41w186 rfl rfl


private theorem pc41w189 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 1 stored91 stored92 rfl rfl
private theorem pc41w191 : PetersenPackedPin.project extra41 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 1 stored89 stored92 rfl rfl
private theorem pc41w188 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 3 pc41w189 pc41w191 rfl rfl
private theorem pc41w192 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
private theorem pc3w193 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w122 pc3w77 rfl rfl
private theorem pc3w194 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w124 pc3w77 rfl rfl
theorem b4_1890 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1890 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1890 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w5 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_1891 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1891 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1891 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w22 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1892 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1892 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1892 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w29 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1893 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1893 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(2,true)),(false,(0,true),(3,true)),(false,(5,true),(0,true))] s4_1893 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w27 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1894 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1894 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1894 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1895 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1895 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1895 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1896 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1896 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1896 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w23 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w36 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_1897 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1897 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1897 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w53 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w45 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_1898 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1898 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1898 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w65 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w61 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1899 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1899 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1899 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w65 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w68 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1900 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1900 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s4_1900 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w65 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w69 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_1901 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1901 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1901 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1902 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1902 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1902 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1903 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1903 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1903 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w89 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1904 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1904 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1904 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w99 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_1905 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1905 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1905 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w53 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w106 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_1906 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1906 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1906 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w53 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w108 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_1907 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1907 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1907 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w109 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1908 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1908 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1908 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w111 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1909 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1909 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1909 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w112 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1910 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1910 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1910 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w115 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1911 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1911 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1911 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w117 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_1912 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1912 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1912 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w117 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w118 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_1913 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1913 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1913 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xf0f0f0f0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w117 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w118 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_1914 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1914 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_1914 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w120 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w119 rfl))))))))) (by decide +kernel)
theorem b4_1915 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1915 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1915 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w122 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1916 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1916 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1916 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w124 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1917 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1917 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_1917 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w133 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w131 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_1918 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1918 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_1918 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xcccccccc] (PetersenWireProjection.cons pc1w133 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w131 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w137 rfl))))))))) (by decide +kernel)
theorem b4_1919 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1919 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_1919 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0x0,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0x0,0xcccccccc] (PetersenWireProjection.cons pc1w133 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w131 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w137 rfl))))))))) (by decide +kernel)
theorem b4_1920 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1920 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1920 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w138 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1921 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1921 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1921 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w139 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1922 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1922 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1922 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1923 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1923 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1923 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w140 rfl))))))))) (by decide +kernel)
theorem b4_1924 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1924 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1924 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w141 rfl))))))))) (by decide +kernel)
theorem b4_1925 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1925 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s4_1925 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w76 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w142 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1926 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1926 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_1926 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xffffffffffffffff,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w159 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons pc107w155 (PetersenWireProjection.cons pc107w149 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_1927 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1927 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_1927 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w173 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons pc39w169 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w163 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_1928 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1928 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_1928 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w188 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons pc41w184 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w177 rfl))))))))) (by decide +kernel)
theorem b4_1929 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1929 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_1929 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w188 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons pc41w184 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w177 (PetersenWireProjection.cons pc41w192 rfl))))))))) (by decide +kernel)
theorem b4_1930 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1930 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1930 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w193 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_1931 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1931 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s4_1931 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w86 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w194 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
