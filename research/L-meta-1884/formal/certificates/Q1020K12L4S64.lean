import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc0w3 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored53 rfl rfl

private theorem pc0w5 : PetersenPackedPin.project cycle0 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored53 rfl rfl
private theorem pc0w2 : PetersenPackedPin.project cycle0 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 pc0w3 pc0w5 rfl rfl


private theorem pc0w9 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w8 : PetersenPackedPin.project cycle0 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc0w9 stored54 rfl rfl




private theorem pc3w14 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl

private theorem pc3w18 : PetersenPackedPin.project cycle3 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored38 rfl rfl

private theorem pc3w20 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored38 rfl rfl
private theorem pc3w17 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 pc3w18 pc3w20 rfl rfl


private theorem pc3w24 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w27 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w28 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 pc3w27 pc3w28 rfl rfl


private theorem pc29w31 : PetersenPackedPin.project extra29 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored153 stored156 rfl rfl


private theorem pc29w33 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl
private theorem pc29w30 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w31 pc29w33 rfl rfl
private theorem pc29w37 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc29w38 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w36 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 0 pc29w37 pc29w38 rfl rfl



private theorem pc29w42 : PetersenPackedPin.project extra29 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 0 stored155 stored154 rfl rfl

private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w46 stored33 rfl rfl
private theorem pc3w44 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w45 pc3w24 rfl rfl
private theorem pc3w49 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w48 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w49 stored33 rfl rfl
private theorem pc3w47 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w48 pc3w24 rfl rfl







private theorem pc1w58 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w59 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc1w57 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w58 pc1w59 rfl rfl

private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w61 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w62 stored33 rfl rfl
private theorem pc3w64 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w64 pc3w24 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w46 stored33 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w49 stored33 rfl rfl
private theorem pc1w67 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored57 stored63 rfl rfl
private theorem pc3w69 : PetersenPackedPin.project cycle3 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 1 stored34 stored36 rfl rfl
private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored35 stored36 rfl rfl
private theorem pc3w68 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xff00ffcc := PetersenWireProjection.derive 2 pc3w69 pc3w70 rfl rfl
private theorem pc3w71 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w49 stored36 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w46 stored37 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w74 stored38 rfl rfl


private theorem pc2w75 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl





private theorem pc2w84 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w85 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 0 stored42 stored47 rfl rfl
private theorem pc2w83 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xaaaa0000 := PetersenWireProjection.derive 3 pc2w84 pc2w85 rfl rfl



private theorem pc69w88 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored97 stored99 rfl rfl


private theorem pc69w91 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored100 rfl rfl
private theorem pc69w87 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc69w88 pc69w91 rfl rfl



private theorem pc69w98 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored97 stored99 rfl rfl
private theorem pc69w97 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w98 pc69w91 rfl rfl

private theorem pc0w100 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w9 stored51 rfl rfl
private theorem pc0w102 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w101 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 3 pc0w102 pc0w9 rfl rfl




private theorem pc30w105 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl



private theorem pc30w112 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 2 stored8 stored10 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xf000f000faaafaaaf000f000faaafaaa := PetersenWireProjection.derive 3 pc30w112 pc30w113 rfl rfl

private theorem pc69w116 : PetersenPackedPin.project extra69 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored99 stored100 rfl rfl
private theorem pc69w115 : PetersenPackedPin.project extra69 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc69w116 stored98 rfl rfl
private theorem pc69w118 : PetersenPackedPin.project extra69 (0x333333330000000000000000000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w116 stored98 rfl rfl
private theorem pc69w117 : PetersenPackedPin.project extra69 (0xcccccccccccccccc3333333300000000cccccccccccccccc3333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w118 pc69w91 rfl rfl
private theorem pc3w120 : PetersenPackedPin.project cycle3 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored38 stored39 rfl rfl
private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w24 pc3w120 rfl rfl




private theorem pc18w125 : PetersenPackedPin.project tree18 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 stored187 stored191 rfl rfl

private theorem pc18w124 : PetersenPackedPin.project tree18 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffffccccffffcccc := PetersenWireProjection.derive 3 pc18w125 stored188 rfl rfl
private theorem pc18w129 : PetersenPackedPin.project tree18 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored186 stored187 rfl rfl
private theorem pc18w123 : PetersenPackedPin.project tree18 (0xfffffffffcfcfcfcf0f0f0f0f0f0f0f0fffffffffcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc18w124 pc18w129 rfl rfl
private theorem pc18w130 : PetersenPackedPin.project tree18 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffccccffffcccc := PetersenWireProjection.derive 3 stored188 stored191 rfl rfl


private theorem pc18w134 : PetersenPackedPin.project tree18 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored186 stored191 rfl rfl
private theorem pc18w135 : PetersenPackedPin.project tree18 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored187 stored191 rfl rfl
private theorem pc18w133 : PetersenPackedPin.project tree18 (0xccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc18w134 pc18w135 rfl rfl

private theorem pc2w138 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w137 : PetersenPackedPin.project cycle2 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w138 stored45 rfl rfl
private theorem pc2w141 : PetersenPackedPin.project cycle2 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored45 stored47 rfl rfl
private theorem pc2w140 : PetersenPackedPin.project cycle2 (0xcc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w138 pc2w141 rfl rfl
private theorem pc2w139 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccc00cc00cccccccccccccccccccccccccc00cc00cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w140 pc2w85 rfl rfl
private theorem pc0w143 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w9 stored49 rfl rfl
private theorem pc0w144 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w142 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 3 pc0w143 pc0w144 rfl rfl
private theorem pc3w146 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w24 stored33 rfl rfl
private theorem pc3w145 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w146 pc3w49 rfl rfl


private theorem pc37w149 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl

private theorem pc37w151 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl
private theorem pc37w148 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 0 pc37w149 pc37w151 rfl rfl

private theorem pc37w153 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl



private theorem pc37w160 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored65 stored71 rfl rfl
private theorem pc37w159 : PetersenPackedPin.project extra37 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c00000000000000000 := PetersenWireProjection.derive 0 pc37w160 stored67 rfl rfl
private theorem pc37w161 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 0 stored66 stored71 rfl rfl
private theorem pc37w158 : PetersenPackedPin.project extra37 (0xcccccccccccccccccccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 pc37w159 pc37w161 rfl rfl

private theorem pc1w165 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored59 stored63 rfl rfl
private theorem pc1w164 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w165 stored57 rfl rfl
private theorem pc1w163 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccc00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 3 pc1w164 pc1w59 rfl rfl
private theorem pc3w167 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w49 stored33 rfl rfl
private theorem pc3w166 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w167 pc3w24 rfl rfl
private theorem pc3w169 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored33 stored35 rfl rfl
private theorem pc3w168 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xffffc0c0 := PetersenWireProjection.derive 3 pc3w169 stored34 rfl rfl
private theorem pc3w170 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w24 stored33 rfl rfl
private theorem pc3w171 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffc0c0 := PetersenWireProjection.derive 3 pc3w169 pc3w14 rfl rfl
private theorem pc3w173 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w24 stored36 rfl rfl
private theorem pc3w172 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w173 pc3w167 rfl rfl
private theorem pc3w175 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w24 stored38 rfl rfl
private theorem pc3w174 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcfcfcfcfcf0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w175 pc3w167 rfl rfl


private theorem pc39w178 : PetersenPackedPin.project extra39 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored73 stored75 rfl rfl

private theorem pc39w177 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w178 stored74 rfl rfl

private theorem pc39w181 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl



private theorem pc39w188 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc0000 := PetersenWireProjection.derive 0 stored75 stored79 rfl rfl
private theorem pc39w187 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c00000c0c00000c0c00000c0c00000 := PetersenWireProjection.derive 0 pc39w188 stored73 rfl rfl
private theorem pc39w189 : PetersenPackedPin.project extra39 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 0 stored74 stored79 rfl rfl
private theorem pc39w186 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccc00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 pc39w187 pc39w189 rfl rfl

private theorem pc39w191 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w178 pc39w181 rfl rfl
private theorem pc3w192 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w24 pc3w49 rfl rfl
private theorem pc3w193 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w46 stored34 rfl rfl
private theorem pc3w195 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w194 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w195 stored34 rfl rfl
private theorem pc3w196 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w64 stored35 rfl rfl
private theorem pc3w197 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w62 stored35 rfl rfl
private theorem pc3w198 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w195 stored35 rfl rfl
theorem b4_2688 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2688 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s4_2688 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w8 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w2 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2689 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2689 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false))] s4_2689 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xc0c0c0c0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons pc3w14 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2690 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2690 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true))] s4_2690 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xcccc,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w24 (PetersenWireProjection.cons pc3w26 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w14 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2691 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2691 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s4_2691 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons pc29w42 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w36 (PetersenWireProjection.cons pc29w30 (PetersenWireProjection.cons stored153 rfl))))))))) (by decide +kernel)
theorem b4_2692 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2692 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2692 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w44 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2693 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2693 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2693 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w47 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2694 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2694 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2694 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2695 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2695 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2695 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w61 rfl))))))))) (by decide +kernel)
theorem b4_2696 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2696 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2696 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 rfl))))))))) (by decide +kernel)
theorem b4_2697 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2697 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2697 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w66 rfl))))))))) (by decide +kernel)
theorem b4_2698 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2698 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2698 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xcccccccc] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w57 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w67 rfl))))))))) (by decide +kernel)
theorem b4_2699 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2699 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,true)),(false,(0,true),(4,true))] s4_2699 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ffcc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w68 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2700 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2700 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2700 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2701 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2701 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2701 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w72 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2702 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2702 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2702 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w63 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w73 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2703 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2703 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(4,false))] s4_2703 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w83 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w75 rfl))))))))) (by decide +kernel)
theorem b4_2704 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2704 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2704 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons pc69w97 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons pc69w87 rfl))))))))) (by decide +kernel)
theorem b4_2705 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2705 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,true))] s4_2705 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xff0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w101 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w100 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2706 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2706 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(5,true)),(false,(4,false),(3,false)),(false,(1,true),(0,true))] s4_2706 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xf000f000faaafaaaf000f000faaafaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2707 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2707 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2707 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons pc69w117 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w115 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2708 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2708 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2708 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w119 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w73 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2709 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2709 := by
  intro m le c
  apply rejects_sound tree18 i6 6 tgt small18 hot18 [(false,(4,true),(1,true))] s4_2709 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0xffffccccffffcccc,0x0,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored192 (PetersenWireProjection.cons pc18w133 (PetersenWireProjection.cons stored190 (PetersenWireProjection.cons stored189 (PetersenWireProjection.cons stored188 (PetersenWireProjection.cons pc18w130 (PetersenWireProjection.cons pc18w123 (PetersenWireProjection.cons stored186 (PetersenWireProjection.cons stored185 rfl))))))))) (by decide +kernel)
theorem b4_2710 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2710 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2710 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w139 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w137 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2711 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2711 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(4,false))] s4_2711 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccc0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w142 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2712 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2712 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2712 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w145 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w28 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2713 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2713 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s4_2713 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons pc37w158 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons pc37w153 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w148 (PetersenWireProjection.cons stored67 rfl))))))))) (by decide +kernel)
theorem b4_2714 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2714 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,false),(2,false))] s4_2714 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xc0c0c0c0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w163 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2715 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2715 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2715 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w14 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2716 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2716 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false)),(false,(0,true),(5,true))] s4_2716 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w168 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2717 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2717 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false)),(false,(0,true),(5,true))] s4_2717 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w168 (PetersenWireProjection.cons pc3w170 rfl))))))))) (by decide +kernel)
theorem b4_2718 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2718 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,false)),(false,(0,true),(5,true))] s4_2718 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w171 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2719 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2719 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false)),(false,(0,true),(5,true))] s4_2719 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w172 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w168 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2720 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2720 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(1,false)),(false,(0,true),(5,true))] s4_2720 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffffc0c0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w166 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w174 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w168 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2721 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2721 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2721 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons pc39w186 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons pc39w181 (PetersenWireProjection.cons pc39w177 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2722 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2722 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2722 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons pc39w186 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored76 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons pc39w177 (PetersenWireProjection.cons pc39w191 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2723 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2723 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2723 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2724 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2724 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2724 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w193 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2725 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2725 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2725 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w194 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2726 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2726 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2726 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w196 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2727 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2727 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2727 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w197 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2728 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2728 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2728 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w198 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2729 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2729 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2729 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w192 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w28 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
