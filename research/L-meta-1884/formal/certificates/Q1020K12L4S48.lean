import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc288w5 : PetersenPackedPin.project extra288 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 stored249 stored250 rfl rfl


private theorem pc288w6 : PetersenPackedPin.project extra288 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored252 stored253 rfl rfl
private theorem pc288w4 : PetersenPackedPin.project extra288 (0x333300003333000033330000333300003333000033330000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 pc288w5 pc288w6 rfl rfl
private theorem pc288w9 : PetersenPackedPin.project extra288 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored251 stored253 rfl rfl
private theorem pc288w3 : PetersenPackedPin.project extra288 (0xffffccccccccccccffffccccccccccccffffccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc288w4 pc288w9 rfl rfl



private theorem pc288w14 : PetersenPackedPin.project extra288 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored249 stored252 rfl rfl
private theorem pc288w15 : PetersenPackedPin.project extra288 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 1 stored250 stored252 rfl rfl
private theorem pc288w13 : PetersenPackedPin.project extra288 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff := PetersenWireProjection.derive 3 pc288w14 pc288w15 rfl rfl





private theorem pc0w20 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored52 stored55 rfl rfl
private theorem pc0w19 : PetersenPackedPin.project cycle0 (0xffffccccffffcccc0000000000000000ffffccccffffcccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w20 stored50 rfl rfl



private theorem pc0w27 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w28 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w26 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w27 pc0w28 rfl rfl





private theorem pc1w33 : PetersenPackedPin.project cycle1 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored60 stored63 rfl rfl
private theorem pc1w32 : PetersenPackedPin.project cycle1 (0xffffccccffffccccffffccccffffcccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w33 stored57 rfl rfl



private theorem pc1w40 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored60 rfl rfl
private theorem pc1w41 : PetersenPackedPin.project cycle1 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored58 stored60 rfl rfl
private theorem pc1w39 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w40 pc1w41 rfl rfl
private theorem pc0w43 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w42 : PetersenPackedPin.project cycle0 (0xffffffffcccccccc0000000000000000ffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w43 stored50 rfl rfl


private theorem pc118w47 : PetersenPackedPin.project extra118 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored257 stored258 rfl rfl


private theorem pc118w48 : PetersenPackedPin.project extra118 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored259 stored260 rfl rfl
private theorem pc118w46 : PetersenPackedPin.project extra118 (0xffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc118w47 pc118w48 rfl rfl




private theorem pc118w55 : PetersenPackedPin.project extra118 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored257 stored264 rfl rfl
private theorem pc118w57 : PetersenPackedPin.project extra118 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored258 stored264 rfl rfl
private theorem pc118w54 : PetersenPackedPin.project extra118 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc118w55 pc118w57 rfl rfl



private theorem pc107w62 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored161 stored166 rfl rfl

private theorem pc107w64 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored162 stored163 rfl rfl
private theorem pc107w61 : PetersenPackedPin.project extra107 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w62 pc107w64 rfl rfl

private theorem pc107w67 : PetersenPackedPin.project extra107 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored167 stored166 rfl rfl
private theorem pc107w66 : PetersenPackedPin.project extra107 (0x33330000000000003333000000000000333300000000000033330000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc107w67 stored163 rfl rfl
private theorem pc107w60 : PetersenPackedPin.project extra107 (0xffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc107w61 pc107w66 rfl rfl



private theorem pc107w73 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored161 stored167 rfl rfl
private theorem pc107w74 : PetersenPackedPin.project extra107 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored162 stored167 rfl rfl
private theorem pc107w72 : PetersenPackedPin.project extra107 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc107w73 pc107w74 rfl rfl




private theorem pc26w78 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl

private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w78 stored2 rfl rfl



private theorem pc26w85 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w85 pc26w87 rfl rfl




private theorem pc30w91 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl

private theorem pc30w90 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w91 stored10 rfl rfl



private theorem pc30w98 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w100 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w97 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w98 pc30w100 rfl rfl
private theorem pc0w101 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored49 stored50 rfl rfl
private theorem pc0w103 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xff0000 := PetersenWireProjection.derive 2 stored49 stored51 rfl rfl
private theorem pc0w102 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w103 stored50 rfl rfl
private theorem pc0w105 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w104 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w105 stored50 rfl rfl
private theorem pc0w107 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored49 stored55 rfl rfl
private theorem pc0w106 : PetersenPackedPin.project cycle0 (0xffffffffffffffff0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w107 stored50 rfl rfl
private theorem pc0w108 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl


private theorem pc41w109 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl

private theorem pc41w112 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl
private theorem pc41w114 : PetersenPackedPin.project extra41 (0xffffffffffffffff0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 0 pc41w112 stored89 rfl rfl





private theorem pc41w120 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 1 stored91 stored92 rfl rfl
private theorem pc41w122 : PetersenPackedPin.project extra41 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 1 stored89 stored92 rfl rfl
private theorem pc41w119 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff := PetersenWireProjection.derive 3 pc41w120 pc41w122 rfl rfl
private theorem pc0w124 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc0w123 : PetersenPackedPin.project cycle0 (0xffffffffffffffff0000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w124 stored50 rfl rfl


private theorem pc39w127 : PetersenPackedPin.project extra39 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored73 stored79 rfl rfl

private theorem pc39w126 : PetersenPackedPin.project extra39 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w127 stored74 rfl rfl





private theorem pc39w135 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w137 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored74 stored76 rfl rfl
private theorem pc39w134 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w135 pc39w137 rfl rfl
private theorem pc39w139 : PetersenPackedPin.project extra39 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored73 stored75 rfl rfl
private theorem pc39w138 : PetersenPackedPin.project extra39 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w139 stored74 rfl rfl
private theorem pc1w142 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w141 : PetersenPackedPin.project cycle1 (0xffff000000000000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc1w142 stored57 rfl rfl
private theorem pc1w140 : PetersenPackedPin.project cycle1 (0xffffffffffffffff000000000000ffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w141 stored58 rfl rfl
private theorem pc39w144 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x33330000333300003333000033330000 := PetersenWireProjection.derive 2 stored75 stored79 rfl rfl
private theorem pc39w143 : PetersenPackedPin.project extra39 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w144 stored74 rfl rfl
private theorem pc1w146 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored59 rfl rfl
private theorem pc1w145 : PetersenPackedPin.project cycle1 (0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w146 stored58 rfl rfl
private theorem pc1w149 : PetersenPackedPin.project cycle1 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored63 rfl rfl
private theorem pc1w148 : PetersenPackedPin.project cycle1 (0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w149 stored58 rfl rfl
private theorem pc1w150 : PetersenPackedPin.project cycle1 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored58 stored60 rfl rfl
private theorem pc1w147 : PetersenPackedPin.project cycle1 (0xffffffffffffffff0000333300003333ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 pc1w148 pc1w150 rfl rfl
private theorem pc1w153 : PetersenPackedPin.project cycle1 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored60 stored63 rfl rfl
private theorem pc1w152 : PetersenPackedPin.project cycle1 (0xcccc0000cccc0000cccc0000cccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w153 stored57 rfl rfl
private theorem pc1w151 : PetersenPackedPin.project cycle1 (0xffffffffffffffff0000cccc0000ccccffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w152 stored58 rfl rfl
private theorem pc1w156 : PetersenPackedPin.project cycle1 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored59 stored60 rfl rfl
private theorem pc1w155 : PetersenPackedPin.project cycle1 (0xffff000000000000ffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w156 stored57 rfl rfl
private theorem pc1w154 : PetersenPackedPin.project cycle1 (0xffffffffffffffff0000ffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w155 stored58 rfl rfl


private theorem pc34w159 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl

private theorem pc34w158 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w159 stored17 rfl rfl





private theorem pc34w168 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w167 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w159 pc34w168 rfl rfl
private theorem pc39w170 : PetersenPackedPin.project extra39 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc := PetersenWireProjection.derive 1 stored75 stored79 rfl rfl
private theorem pc39w169 : PetersenPackedPin.project extra39 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w170 stored74 rfl rfl
private theorem pc26w171 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc39w174 : PetersenPackedPin.project extra39 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored76 rfl rfl
private theorem pc39w173 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc39w174 stored73 rfl rfl
private theorem pc39w175 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl
private theorem pc39w172 : PetersenPackedPin.project extra39 (0xffffffffffffffffcccc0000cccc0000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc39w173 pc39w175 rfl rfl
private theorem pc39w177 : PetersenPackedPin.project extra39 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc0000 := PetersenWireProjection.derive 0 stored75 stored79 rfl rfl
private theorem pc39w176 : PetersenPackedPin.project extra39 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w177 stored74 rfl rfl
private theorem pc1w179 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w178 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w179 stored58 rfl rfl
private theorem pc0w180 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc34w182 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w181 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccffffccccffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w159 pc34w182 rfl rfl
private theorem pc26w183 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w78 stored1 rfl rfl
private theorem pc30w184 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w185 : PetersenPackedPin.project extra30 (0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 pc30w91 stored9 rfl rfl



private theorem pc32w187 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl





private theorem pc32w195 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w197 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w194 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc32w195 pc32w197 rfl rfl
private theorem pc32w199 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w198 : PetersenPackedPin.project extra32 (0xffffffffffffffffffccffccffccffccffffffffffffffffffccffccffccffcc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc32w199 stored25 rfl rfl
private theorem pc39w201 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored75 rfl rfl
private theorem pc39w200 : PetersenPackedPin.project extra39 (0xffffffffffffffffffff000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc39w173 pc39w201 rfl rfl
private theorem pc1w203 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl
private theorem pc1w202 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc1w203 stored58 rfl rfl
private theorem pc0w204 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl
theorem b4_2016 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2016 := by
  intro m le c
  apply rejects_sound extra288 i5 4 tgt small288 hot288 [] s4_2016 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff,0xaaaaaaaa,0x0,0xff00ff00,0xffff0000,0x0,0xcccccccc,0xffffffff,0xf0f0f0f0] (PetersenWireProjection.cons pc288w13 (PetersenWireProjection.cons stored256 (PetersenWireProjection.cons stored253 (PetersenWireProjection.cons stored255 (PetersenWireProjection.cons stored254 (PetersenWireProjection.cons pc288w3 (PetersenWireProjection.cons stored251 (PetersenWireProjection.cons stored250 (PetersenWireProjection.cons stored249 rfl))))))))) (by decide +kernel)
theorem b4_2017 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2017 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2017 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w19 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2018 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2018 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2018 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w32 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2019 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2019 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2019 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w42 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2020 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2020 := by
  intro m le c
  apply rejects_sound extra118 i5 4 tgt small118 hot118 [] s4_2020 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccc,0xaaaaaaaa,0xffff0000,0xff00ff00,0xf0f0f0f0,0x0,0x0,0x0] (PetersenWireProjection.cons pc118w54 (PetersenWireProjection.cons stored263 (PetersenWireProjection.cons stored260 (PetersenWireProjection.cons stored262 (PetersenWireProjection.cons stored261 (PetersenWireProjection.cons stored259 (PetersenWireProjection.cons pc118w46 (PetersenWireProjection.cons stored258 (PetersenWireProjection.cons stored257 rfl))))))))) (by decide +kernel)
theorem b4_2021 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2021 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_2022 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2022 := by
  apply node_sound (nxt := [s5_31,s5_29])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_31 theta
    · exact b5_29 theta
theorem b4_2023 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2023 := by
  intro m le c
  apply rejects_sound extra107 i6 5 tgt small107 hot107 [] s4_2023 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc107w72 (PetersenWireProjection.cons stored168 (PetersenWireProjection.cons stored166 (PetersenWireProjection.cons stored165 (PetersenWireProjection.cons stored164 (PetersenWireProjection.cons stored163 (PetersenWireProjection.cons pc107w60 (PetersenWireProjection.cons stored162 (PetersenWireProjection.cons stored161 rfl))))))))) (by decide +kernel)
theorem b4_2024 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2024 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,true),(8,true))] s4_2024 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2025 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2025 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true)),(false,(5,true),(2,true))] s4_2025 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w97 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w90 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2026 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2026 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2026 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w101 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2027 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2027 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2027 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w102 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2028 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2028 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2028 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w104 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2029 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2029 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2029 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w106 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2030 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2030 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2030 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w106 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w108 rfl))))))))) (by decide +kernel)
theorem b4_2031 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2031 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_2031 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w119 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons pc41w114 (PetersenWireProjection.cons pc41w112 (PetersenWireProjection.cons pc41w109 rfl))))))))) (by decide +kernel)
theorem b4_2032 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2032 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2032 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w123 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2033 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2033 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2033 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w126 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2034 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2034 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2034 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w138 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2035 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2035 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2035 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w140 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2036 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2036 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2036 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w143 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2037 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2037 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2037 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w145 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2038 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2038 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2038 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w147 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2039 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2039 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2039 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w151 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2040 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2040 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2040 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w154 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2041 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2041 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s4_2041 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w167 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w158 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2042 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2042 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2042 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w169 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2043 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2043 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2043 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w148 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2044 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2044 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_2044 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w171 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2045 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2045 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2045 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w172 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2046 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2046 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2046 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w176 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2047 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2047 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2047 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w178 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2048 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2048 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2048 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w180 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2049 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2049 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s4_2049 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w167 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w181 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_2050 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2050 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,true),(2,true))] s4_2050 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w183 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2051 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2051 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_2051 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w97 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w184 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2052 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2052 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true)),(false,(5,true),(4,true))] s4_2052 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w97 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w185 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_2053 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2053 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,false),(4,true)),(false,(0,true),(5,true)),(false,(5,true),(0,true))] s4_2053 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w194 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w187 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2054 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2054 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true)),(false,(2,true),(6,true))] s4_2054 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w194 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w198 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_2055 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2055 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s4_2055 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc39w134 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w200 (PetersenWireProjection.cons stored73 rfl))))))))) (by decide +kernel)
theorem b4_2056 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2056 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_2056 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xffff0000,0xf0f0f0f0,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w39 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w202 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2057 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2057 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2057 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0xffff0000,0xff00ff00] (PetersenWireProjection.cons pc0w26 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w204 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
