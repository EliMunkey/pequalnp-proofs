import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S6
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S19
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S25
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S30
import Q1020K12L4S53
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S69
import Q1020K12L4S73
import Q1020K12L4S74
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc29w1 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl

private theorem pc29w0 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w1 stored153 rfl rfl
private theorem pc29w5 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl





private theorem pc29w11 : PetersenPackedPin.project extra29 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f := PetersenWireProjection.derive 1 pc29w1 stored153 rfl rfl



private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl

private theorem pc26w16 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl




private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc26w13 stored0 rfl rfl



private theorem pc30w24 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl

private theorem pc30w27 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl




private theorem pc30w33 : PetersenPackedPin.project extra30 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff000000000fff0fff0 := PetersenWireProjection.derive 1 pc30w27 stored8 rfl rfl




private theorem pc117w36 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored123 stored124 rfl rfl




private theorem pc117w44 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc117w36 stored122 rfl rfl
private theorem pc117w43 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc117w44 stored121 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0xaaaaaaaa000000000000000000000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w48 stored1 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w47 pc26w49 rfl rfl
private theorem pc26w50 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc26w45 stored0 rfl rfl



private theorem pc3w52 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl





private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w61 : PetersenPackedPin.project cycle3 (0xcccccccc000000000000000000000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w62 stored34 rfl rfl
private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w60 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w61 pc3w63 rfl rfl
private theorem pc30w64 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w67 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored10 stored13 rfl rfl
private theorem pc30w66 : PetersenPackedPin.project extra30 (0xf0f0f0f0000000000000000000000000f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w67 stored9 rfl rfl
private theorem pc30w68 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc30w65 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w66 pc30w68 rfl rfl



private theorem pc32w70 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl





private theorem pc32w80 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored26 stored28 rfl rfl
private theorem pc32w79 : PetersenPackedPin.project extra32 (0xff00ff00000000000000000000000000ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc32w80 stored25 rfl rfl
private theorem pc32w81 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored24 stored28 rfl rfl
private theorem pc32w78 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w79 pc32w81 rfl rfl



private theorem pc34w83 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl





private theorem pc34w93 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored18 stored19 rfl rfl
private theorem pc34w92 : PetersenPackedPin.project extra34 (0xffff0000000000000000000000000000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w93 stored17 rfl rfl
private theorem pc34w94 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored16 stored19 rfl rfl
private theorem pc34w91 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w92 pc34w94 rfl rfl
private theorem pc26w97 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w96 : PetersenPackedPin.project extra26 (0x222222222222222200000000000000002222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w97 stored1 rfl rfl
private theorem pc26w95 : PetersenPackedPin.project extra26 (0x2222222222222222aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w96 pc26w49 rfl rfl
private theorem pc30w100 : PetersenPackedPin.project extra30 (0x3030303030303030303030303030303030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored13 stored14 rfl rfl
private theorem pc30w99 : PetersenPackedPin.project extra30 (0x303030303030303000000000000000003030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w100 stored9 rfl rfl
private theorem pc30w98 : PetersenPackedPin.project extra30 (0x3030303030303030f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w99 pc30w68 rfl rfl



private theorem pc2w102 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl





private theorem pc2w112 : PetersenPackedPin.project cycle2 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored43 stored47 rfl rfl
private theorem pc2w111 : PetersenPackedPin.project cycle2 (0x333333330000000000000000000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc2w112 stored42 rfl rfl
private theorem pc2w113 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored41 stored43 rfl rfl
private theorem pc2w110 : PetersenPackedPin.project cycle2 (0x3333333300000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc2w111 pc2w113 rfl rfl
private theorem pc30w115 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffffffffff0000ffffffffffff0000 := PetersenWireProjection.derive 3 stored8 stored15 rfl rfl
private theorem pc30w116 : PetersenPackedPin.project extra30 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored9 stored15 rfl rfl
private theorem pc30w114 : PetersenPackedPin.project extra30 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xfffff0f0ffff0000fffff0f0ffff0000 := PetersenWireProjection.derive 0 pc30w115 pc30w116 rfl rfl
private theorem pc30w118 : PetersenPackedPin.project extra30 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f000000000 := PetersenWireProjection.derive 0 stored8 stored9 rfl rfl
private theorem pc30w119 : PetersenPackedPin.project extra30 (0x5050505050505050505050505050505050505050505050505050505050505050 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored13 stored15 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0x505050505050505050505050505050505050505050505050 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w118 pc30w119 rfl rfl
private theorem pc34w121 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored16 stored23 rfl rfl
private theorem pc34w122 : PetersenPackedPin.project extra34 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored17 stored23 rfl rfl
private theorem pc34w120 : PetersenPackedPin.project extra34 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 0 pc34w121 pc34w122 rfl rfl
private theorem pc34w124 : PetersenPackedPin.project extra34 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored16 stored17 rfl rfl
private theorem pc34w125 : PetersenPackedPin.project extra34 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored19 stored23 rfl rfl
private theorem pc34w123 : PetersenPackedPin.project extra34 (0x555500005555000055550000555500005555000055550000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc34w124 pc34w125 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w49 pc26w128 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w130 : PetersenPackedPin.project extra26 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored0 stored1 rfl rfl
private theorem pc2w131 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w133 : PetersenPackedPin.project cycle2 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f00000 := PetersenWireProjection.derive 0 stored41 stored42 rfl rfl
private theorem pc2w132 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w133 pc2w131 rfl rfl


private theorem pc0w136 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored49 stored50 rfl rfl






private theorem pc0w144 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w143 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 2 pc0w136 pc0w144 rfl rfl
private theorem pc3w145 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w147 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w146 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w63 pc3w147 rfl rfl
private theorem pc3w148 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc0w149 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w151 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w152 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w150 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc0w151 pc0w152 rfl rfl
private theorem pc30w153 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w155 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored9 stored13 rfl rfl
private theorem pc30w154 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w68 pc30w155 rfl rfl
private theorem pc30w156 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc34w157 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w159 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored17 stored19 rfl rfl
private theorem pc34w158 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w94 pc34w159 rfl rfl
private theorem pc34w160 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl




private theorem pc69w163 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl




private theorem pc69w171 : PetersenPackedPin.project extra69 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0 := PetersenWireProjection.derive 0 stored97 stored98 rfl rfl
private theorem pc69w170 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc69w171 pc69w163 rfl rfl
theorem b3_1680 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1680 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1680 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w11 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w5 (PetersenWireProjection.cons pc29w0 rfl)))))))))) (by decide +kernel)
theorem b3_1681 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1681 := by
  apply PetersenIndexedNode.close (bank := [s4_2925,a4676,s4_1155,s4_1137,a4697,a4698,a4699,a4700,s4_1166,s4_1154,a4701,a4702,s4_1143,a4703,a4696]) (PetersenIndexedNode.reasons 256 17 414 0x2001d000d620221010840442025010084054000840415052800140402a0a150521010420221013111084044202420230a090808c444614121111080842022101480840031200084042820240012020504048082101200168404290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210146060a0811808840415112101118182a224206210105040840425050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e08131103830141814100504028204202400290800901003012100108080602030124042001290108003818080c04420262601080a0010c4c04260108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060280034001506028404212020c0484048381210132220848042402101109008404c88841c09202854144240150508404c4c02101150518980541421012120084052504424021201410200065040494140011210450402120109005444424015110a08117122820151122e245444282021200a0800c0442400301212008c8846400301119100c0484802120109010a0a212042822101006040302428280c080604840410902101193120302018110808c2c0420264c498580c2c04202018100c084202030210800a0204240210010808848042022808018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090109000604030221a080c080604424010900848200050001800021011242484042101248488404c2826222211108404c444210130a092424c202150524848541421015111084045414a2225101084052424210128202888944449080490924848a080921249012420144449202151124849242428204d0d2486854449a1a4d090a081242492120301248480c0484806222311100c04c444030121201242486022120311112024838149092404884809212490920e058888c2400181248480604212062a2884800604c54501810848124248302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2925 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2918 theta)
    · exact b4_1155 theta
    · exact b4_1137 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1166 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1062 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1060 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1137 theta)
    · exact b4_1166 theta
    · exact b4_1154 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1143 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1154 theta)
    · exact b4_1143 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1062 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1060 theta)
theorem b3_1682 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1682 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1682 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1683 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1683 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true)),(false,(6,true),(0,true))] s3_1683 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w33 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1684 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1684 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true)),(false,(6,true),(0,true))] s3_1684 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w33 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1685 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1685 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1685 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons pc117w43 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons pc117w36 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1686 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1686 := by
  apply PetersenIndexedNode.close (bank := [s4_1155,a4065,a4704,s4_2912,a4705,s4_1182]) (PetersenIndexedNode.reasons 256 17 173 0x1000442024001508084202420230a08840470302101280014000a08042022820054142a0a5040188088404422221012400120009010420224200a08050404840148088404421221010e82854142a1a1505230110808840c42020a08054442a221410128088404420a21010a80854042a0a24200a08070402830141021001080084040301212000c0406024240018088404c4c00301018084c0406220301018082c0406120301018081c04060a0301109010808c2c04202098904c48420221201202854146240150510900848050404941109005444282015110a0800c04464003011090006048404420280c08424003020181084800604420230b000c0806042302109000c0806041302018900c0806040b02018500c0806040602109200c08424003020181084812424840480014000600070000210130a088404c2821080884045414a080282024200a08090801410323005040c8c00301212000c048480212030b008480c2c0018120e0806048382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1155 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2771 theta)
    · exact b4_2912 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_202 theta)
    · exact b4_1182 theta
theorem b3_1687 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1687 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1687 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w43 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w44 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1688 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1688 := by
  apply PetersenIndexedNode.close (bank := [s4_455,a4706,a4707,s4_2533,s4_704,a4708,a4339,s4_2819,s4_868,a4709,a4710,a4711,a4712,s4_392,a4713,a4714,a4715,s4_284,a4716,a4717,s4_960,s4_222,a4527,a4105,a4674,s4_155,a4675,a4079,s4_3,s4_2926,s4_1183,a4718,s4_1180,a4719,s4_1181,a4720,a4721]) (PetersenIndexedNode.reasons 256 17 426 0x20046420221012101185048404801230a098504840421011080a00422a0a5000210114100a00080112820141008404150521010c4442a0a310110808c282420231111850484444202150510809202050404800210112100900048082420120208404282021010a4249080290110808a080420229091410084244202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a8291818282046022101191808404460632301081884041410210109414282025011080890804202250512100841442021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a081080806024200240410900840042022120108089010030101808e8680602030110809898042023a1a31300e0684202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a003e26244180a101107028301801020e05070284041312210108404262421011c0c08480622021011090084047030131212028541442401505185044c4826241505098905014614121200a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0442400301212004c4826200301098900c0484802120109010a0a0302018121011070484044282a0e09080a8404018100c0993120302018110808c2c0420264c49858042c04202018100c08c282030201810a8284240230230a08848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090098900604030221a080c0806042624109008482003d001d490921012003884042101400688404c282800c920208405001b210130a0a0030c2821505400584202a080800a88404541500171505282020028a080282040048a08090808008a4200a0810013282024202002090801410400385040c8c08006b23005041000f1410323020018c8c00301400280c0484808004a12000c05000b0301212020010848013124001806028381800280c044c490007131220e0600088381018140008060483828000a0e0806050003018120e0a00008382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_455 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_392 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2384 theta)
    · exact b4_2533 theta
    · exact b4_704 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_155 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2819 theta
    · exact b4_868 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_284 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2268 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2575 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_455 theta)
    · exact b4_392 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2384 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2533 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_868 theta)
    · exact b4_284 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2268 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2575 theta)
    · exact b4_960 theta
    · exact b4_222 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2668 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2832 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_704 theta)
    · exact b4_155 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2613 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2819 theta)
    · exact b4_3 theta
    · exact b4_2926 theta
    · exact b4_1183 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_665 theta)
    · exact b4_1180 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_919 theta)
    · exact b4_1181 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_665 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1180 theta)
theorem b3_1689 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1689 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s3_1689 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1690 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1690 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true)),(false,(0,true),(3,false))] s3_1690 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a0,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1691 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1691 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s3_1691 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1692 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1692 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_1692 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons pc3w60 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w52 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1693 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1693 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(2,true))] s3_1693 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w65 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w64 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1694 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1694 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(4,true))] s3_1694 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w78 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1695 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1695 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true))] s3_1695 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w91 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1696 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1696 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s3_1696 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w95 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1697 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1697 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true))] s3_1697 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w98 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1698 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1698 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,true),(4,true))] s3_1698 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffffaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc2w110 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w102 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1699 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1699 := by
  apply PetersenIndexedNode.close (bank := [a4722,a4723,s4_1231,s4_1225,a4724,a4725,a4726,s4_1226,s4_1211,a4727,a4728,s4_1227,s4_1207,a4729,a4730,s4_1228,a4731,a4732,a4733,a4734,a4735,a4736,a4737,a4738,s4_1234,a4739,a4740,a4741,a4742,a4743,s4_1237,a4744,a4745,s4_1230,s4_1235,s4_1232,s4_1229,s4_456,s4_1236]) (PetersenIndexedNode.reasons 256 17 417 0x850510902141108090025420221416004c84054202084810808c4452101108090808c889420231115911284444202108088404616021011080842404909248418580921248091090108088404a0201080a80010808a0805000280814100a02042020840442022120140408402004821011080084804202210180118a0205010622210808840484046141308098888c28242222101084044202901028202400108089080480024041210090104202141010808313028200c4804240514110900c4c0a28221301090141004240501048401400084045040280014040a08050102101242008404311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a0810809002114100a080424049411090400889282484110900a08042404808141012000840448402400120209080480821010a0808404280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c042524030101808424085811090094910b0221241090018080c044c0c0301018088404c4c02101130318980480c2101018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c049212018080c05080883814180a484907029212420200c0406030020800f80c020030030101808848200042120210100c040602480821a090c048404434121011202006020301150500c0406022101800e884045415001e15050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c0406028480038281c040c0407050301212000602030149094006d24248404800d210112425001c49092101200328404800c4005c06042120800000c088405001521011202200284808210140058840448088009920205415001115050840600202101150540048541421018007884052505000d49411410200185040494140039250450408005941005445000915110a082001028201511400285444282080038a0800c050005030121202000884800301400180c0484808001a120200050001030200c0600000301)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_8 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2654 theta)
    · exact b4_1231 theta
    · exact b4_1225 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1212 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2338 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2537 theta)
    · exact b4_1226 theta
    · exact b4_1211 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2336 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2538 theta)
    · exact b4_1227 theta
    · exact b4_1207 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2341 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2578 theta)
    · exact b4_1228 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_165 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2657 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2835 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_292 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_324 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2665 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2841 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3114 theta)
    · exact b4_1234 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_291 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_351 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2664 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2843 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_561 theta)
    · exact b4_1237 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_893 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_894 theta)
    · exact b4_1230 theta
    · exact b4_1235 theta
    · exact b4_1232 theta
    · exact b4_1229 theta
    · exact b4_456 theta
    · exact b4_1236 theta
theorem b3_1700 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1700 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(2,false)),(false,(0,true),(5,true))] s3_1700 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0ffff0000fffff0f0ffff0000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w117 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w114 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1701 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1701 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_1701 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w123 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w120 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1702 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1702 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s3_1702 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1703 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1703 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s3_1703 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1704 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1704 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(1,false),(3,false))] s3_1704 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w130 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1705 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1705 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s3_1705 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1706 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1706 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,false)),(false,(5,true),(7,true))] s3_1706 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons pc26w130 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1707 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1707 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s3_1707 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_1708 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1708 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1708 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w132 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w131 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_1709 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1709 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(4,false))] s3_1709 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccc0000,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w143 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1710 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1710 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_1710 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w132 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_1711 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1711 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1711 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w146 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w145 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1712 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1712 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1712 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w146 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w148 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1713 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1713 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(4,true))] s3_1713 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffffcccc,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w150 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w149 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1714 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1714 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_1714 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w146 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w148 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_1715 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1715 := by
  apply PetersenIndexedNode.close (bank := [s4_1251,s4_1250,s4_1249,s4_1240,s4_1239,s4_1238,s4_2410,s4_2534,a4746,a4516,a4747,s4_2799,s4_1263,a4748,a4749,a4750,a4751,s4_1213,a4752,a4753,s4_1266,s4_1208,a4754,a4755,s4_1270,a4756,a4757,a4758,a4528,a4759,a4529,s4_2912,a4760,s4_1005,a4761,a4530,s4_1278,a4762,a4763,s4_1279]) (PetersenIndexedNode.reasons 256 17 432 0x622212021880884046444210118888c8884222210109010840451110a829400084045040280014444a0805111210105414840431110a828c4044808706018808c444e0c0311112020541448084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a0205040280812021210048081d0d1410074142a0a38300a82874347060150d0a828a0802a0a46060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050101505121005404a08014100a80854142820150528200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c0406028013018080c042a0a13110980a004e262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490909891242484046160210112424c2c04909210104c48840431110989084004808212010800c44442403111120204c4848081505109005414a080131209890541426241405282008480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080120a0805445002514110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c0806042a0a109008c094302212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120490940089242484048010a10112425002349092101200408404311140078c4444808800e92020c445001f210112022003842021505400684202a080800c884045415001b1505282020030a080383040058e0c05040800a94100e0c10017383014102002850401410400485040484080089210050410013141012102002048400301400380c0484808006a12000c05000f0301212020018848013124002806024240800480c044c49000b131210902001042400181400180605000580024000c0605000701814000a00030000)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1251 theta
    · exact b4_1250 theta
    · exact b4_1249 theta
    · exact b4_1240 theta
    · exact b4_1239 theta
    · exact b4_1238 theta
    · exact b4_2410 theta
    · exact b4_2534 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1270 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2607 theta)
    · exact b4_2799 theta
    · exact b4_1263 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1213 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2295 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2576 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1263 theta)
    · exact b4_1213 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2295 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2576 theta)
    · exact b4_1266 theta
    · exact b4_1208 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2252 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2587 theta)
    · exact b4_1270 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_97 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2607 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2799 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_505 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1005 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2629 theta)
    · exact b4_2912 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_505 theta)
    · exact b4_1005 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2629 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2912 theta)
    · exact b4_1278 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1279 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1278 theta)
    · exact b4_1279 theta
theorem b3_1716 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1716 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(3,false))] s3_1716 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w154 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w153 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1717 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1717 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true))] s3_1717 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w154 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w156 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1718 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1718 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s3_1718 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w158 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w157 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1719 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1719 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s3_1719 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w158 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w160 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1720 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1720 := by
  apply PetersenIndexedNode.close (bank := [s4_1253,s4_1241,s4_2402,s4_2535,s4_1269,a4764,a4765,s4_2824,s4_1281,a4766,a4767,a4768,a4769,s4_1214,a4770,a4771,s4_1287,s4_1209,a4772,a4773,s4_1292,s4_3105,a4774,s4_1293,a4775,s4_204,a4776,a4350,s4_533,a4777,a4351,a4778,a4779,s4_830,a4780,a4352]) (PetersenIndexedNode.reasons 256 17 432 0x622210808840484046141210118888c2824222210108404420250100a829440484047060288094040e0c05010210105414840431110a828c202420230a098404c4446141211110808541442024808141012000840448402400120209080480821010a0808404280824200a0004202282014000a0205040280810809210042021d0d1410074142a0a38300a82874347060150d0a828a0802a0a46060a081180884046460210111818c8c04206210105040840424040a0809000420224201200090104840240410808504042021505121005404614114100a80854142820150518504908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0442026260108089818c4c02406108080c04060232a2818080c042a0a131109808ca8a262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406025111098910602840441c0a0c05444483815011210104c488404210109890840448086160120208404c2c02101120204c484808150520e0454146141131209890541426241405185050702280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c482820030120e040c0484801312098800c04262403012120107028480428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b010808921261602404908080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c090702030201810989042402120501040089404084048010a1011404100234909210120040840421014007884044808800e920208405001f2101120220038480815054006842026141800c884045415001b15051850600306141800a4004e00245040800894102002f0016800a9410200205040141040038504048408006921005041000f141012102001848400301400280c0484808004a12000c05000b0301212020010848013124001806028381800280c044c490007131220e0600088381018140008060461608000985800605000301811858200006160)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1253 theta
    · exact b4_1241 theta
    · exact b4_2402 theta
    · exact b4_2535 theta
    · exact b4_1269 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_204 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2606 theta)
    · exact b4_2824 theta
    · exact b4_1281 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1214 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2311 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2546 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1281 theta)
    · exact b4_1214 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2311 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2546 theta)
    · exact b4_1287 theta
    · exact b4_1209 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2251 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2250 theta)
    · exact b4_1292 theta
    · exact b4_3105 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2588 theta)
    · exact b4_1293 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1269 theta)
    · exact b4_204 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2606 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2824 theta)
    · exact b4_533 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_830 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2640 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2898 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_533 theta)
    · exact b4_830 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2640 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2898 theta)
theorem b3_1721 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1721 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_1721 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons pc69w170 (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w163 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
