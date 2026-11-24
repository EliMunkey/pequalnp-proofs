import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S6
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S25
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S40
import Q1020K12L4S41
import Q1020K12L4S54
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc34w0 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl






private theorem pc34w9 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w11 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w10 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w11 stored16 rfl rfl
private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffffffffffffffffffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w13 stored16 rfl rfl
private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w16 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w15 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc34w16 stored18 rfl rfl
private theorem pc34w17 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w19 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc34w18 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 2 pc34w9 pc34w19 rfl rfl
private theorem pc34w21 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored16 stored20 rfl rfl
private theorem pc34w22 : PetersenPackedPin.project extra34 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored17 stored20 rfl rfl
private theorem pc34w20 : PetersenPackedPin.project extra34 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ffffff00ffffff00ff00ff00ff00 := PetersenWireProjection.derive 1 pc34w21 pc34w22 rfl rfl
private theorem pc34w24 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored18 stored22 rfl rfl
private theorem pc34w23 : PetersenPackedPin.project extra34 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc34w24 stored20 rfl rfl
private theorem pc34w25 : PetersenPackedPin.project extra34 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc34w16 stored20 rfl rfl
private theorem pc34w27 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w26 : PetersenPackedPin.project extra34 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffaaffaaffaaffaaff00ff00ff00ff00 := PetersenWireProjection.derive 3 pc34w27 stored20 rfl rfl
private theorem pc34w29 : PetersenPackedPin.project extra34 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored18 stored20 rfl rfl
private theorem pc34w28 : PetersenPackedPin.project extra34 (0xffffffffff00ff00ffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfff0fff0fff0fff0ff00ff00ff00ff00 := PetersenWireProjection.derive 0 pc34w21 pc34w29 rfl rfl
private theorem pc34w31 : PetersenPackedPin.project extra34 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored21 rfl rfl
private theorem pc34w32 : PetersenPackedPin.project extra34 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffff0000ffffffffffff0000 := PetersenWireProjection.derive 3 stored17 stored21 rfl rfl
private theorem pc34w30 : PetersenPackedPin.project extra34 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffffffff0000 := PetersenWireProjection.derive 2 pc34w31 pc34w32 rfl rfl
private theorem pc34w34 : PetersenPackedPin.project extra34 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored18 stored22 rfl rfl
private theorem pc34w33 : PetersenPackedPin.project extra34 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 3 pc34w34 stored21 rfl rfl
private theorem pc34w35 : PetersenPackedPin.project extra34 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffaaaa0000ffffffffaaaa0000 := PetersenWireProjection.derive 3 pc34w16 stored21 rfl rfl
private theorem pc34w37 : PetersenPackedPin.project extra34 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored21 rfl rfl
private theorem pc34w36 : PetersenPackedPin.project extra34 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f00000fffffffff0f00000 := PetersenWireProjection.derive 0 pc34w32 pc34w37 rfl rfl
private theorem pc34w39 : PetersenPackedPin.project extra34 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored16 stored21 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xfffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0ffffffff00000000 := PetersenWireProjection.derive 0 pc34w39 pc34w37 rfl rfl
private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafafafafafaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 0 pc34w14 pc34w17 rfl rfl
private theorem pc34w42 : PetersenPackedPin.project extra34 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored17 stored23 rfl rfl
private theorem pc34w43 : PetersenPackedPin.project extra34 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored18 stored23 rfl rfl
private theorem pc34w41 : PetersenPackedPin.project extra34 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 1 pc34w42 pc34w43 rfl rfl
private theorem pc34w45 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored16 stored23 rfl rfl
private theorem pc34w46 : PetersenPackedPin.project extra34 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored22 stored23 rfl rfl
private theorem pc34w44 : PetersenPackedPin.project extra34 (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xddddddddddddddddcccccccccccccccc := PetersenWireProjection.derive 1 pc34w45 pc34w46 rfl rfl
private theorem pc34w48 : PetersenPackedPin.project extra34 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored22 stored23 rfl rfl
private theorem pc34w47 : PetersenPackedPin.project extra34 (0xeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 0 pc34w42 pc34w48 rfl rfl
private theorem pc34w50 : PetersenPackedPin.project extra34 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored18 stored23 rfl rfl
private theorem pc34w49 : PetersenPackedPin.project extra34 (0xffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xfcfcfcfcfcfcfcfccccccccccccccccc := PetersenWireProjection.derive 0 pc34w45 pc34w50 rfl rfl
private theorem pc34w51 : PetersenPackedPin.project extra34 (0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 0 pc34w45 pc34w42 rfl rfl
private theorem pc34w53 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w52 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w53 stored17 rfl rfl
private theorem pc34w56 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w55 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w56 stored16 rfl rfl
private theorem pc34w54 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w55 pc34w9 rfl rfl
private theorem pc34w58 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w58 stored17 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc34w61 stored16 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000ffff00000000 : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w60 pc34w9 rfl rfl
private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffffffffffffffff00000000ccccccccffffffffffffffff00000000cccccccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 3 pc34w24 stored17 rfl rfl
private theorem pc34w64 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc34w56 stored18 rfl rfl
private theorem pc34w63 : PetersenPackedPin.project extra34 (0xffff0000ffff000000000000cccc0000ffff0000ffff000000000000cccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 3 pc34w64 pc34w9 rfl rfl
private theorem pc34w66 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 1 stored16 stored18 rfl rfl
private theorem pc34w65 : PetersenPackedPin.project extra34 (0xffffffffffffffff00000000ffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w66 stored17 rfl rfl
private theorem pc34w68 : PetersenPackedPin.project extra34 (0xffff000000000000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 pc34w19 stored16 rfl rfl
private theorem pc34w67 : PetersenPackedPin.project extra34 (0xffff0000ffff000000000000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w68 pc34w9 rfl rfl
private theorem pc34w69 : PetersenPackedPin.project extra34 (0xffffffffffffffff3333333300000000ffffffffffffffff3333333300000000 : BitVec 256) = 0xffff5050ffff5050ffff5050ffff5050 := PetersenWireProjection.derive 3 pc34w34 stored17 rfl rfl
private theorem pc34w72 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w71 : PetersenPackedPin.project extra34 (0x333300000000000033330000000000003333000000000000333300000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 2 pc34w72 stored18 rfl rfl
private theorem pc34w70 : PetersenPackedPin.project extra34 (0xffff0000ffff00003333000000000000ffff0000ffff0000333300000000 : BitVec 256) = 0xffff5050ffff5050ffff5050ffff5050 := PetersenWireProjection.derive 3 pc34w71 pc34w9 rfl rfl
private theorem pc34w74 : PetersenPackedPin.project extra34 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 1 stored16 stored22 rfl rfl
private theorem pc34w73 : PetersenPackedPin.project extra34 (0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000 : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w74 stored17 rfl rfl
private theorem pc34w77 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 2 stored17 stored22 rfl rfl
private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffffccccffffccccffff0000ffff0000ffffccccffffcccc : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 3 pc34w77 stored19 rfl rfl
private theorem pc34w75 : PetersenPackedPin.project extra34 (0xffff0000ffff00003333000033330000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 2 pc34w76 pc34w0 rfl rfl
private theorem pc34w79 : PetersenPackedPin.project extra34 (0xffff0000ffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc34w9 stored16 rfl rfl
private theorem pc34w80 : PetersenPackedPin.project extra34 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 2 stored19 stored23 rfl rfl
private theorem pc34w78 : PetersenPackedPin.project extra34 (0xffff0000ffff0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc34w79 pc34w80 rfl rfl
private theorem pc34w82 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w81 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0 := PetersenWireProjection.derive 3 pc34w82 stored17 rfl rfl
private theorem pc34w84 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc34w56 stored18 rfl rfl
private theorem pc34w83 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc000000000000ffff0000ffff0000cccc00000000 : BitVec 256) = 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0 := PetersenWireProjection.derive 3 pc34w84 pc34w9 rfl rfl
private theorem pc34w85 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 0 pc34w14 pc34w11 rfl rfl
private theorem pc34w87 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w11 stored19 rfl rfl
private theorem pc34w86 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 0 pc34w87 pc34w14 rfl rfl
theorem b3_2142 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2142 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_2142 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w0 rfl))))))))) (by decide +kernel)
theorem b3_2143 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2143 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_2143 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffffaaaaffffaaaa] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w0 (PetersenWireProjection.cons pc34w10 rfl)))))))))) (by decide +kernel)
theorem b3_2144 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2144 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(0,false),(3,true))] s3_2144 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w0 (PetersenWireProjection.cons pc34w12 rfl)))))))))) (by decide +kernel)
theorem b3_2145 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2145 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_2145 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w14 (PetersenWireProjection.cons pc34w0 rfl))))))))) (by decide +kernel)
theorem b3_2146 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2146 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false)),(false,(0,true),(3,true))] s3_2146 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w15 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2147 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2147 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_2147 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w13 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2148 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2148 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true))] s3_2148 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f00000f0f00000f0f00000f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w18 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2149 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2149 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(4,true)),(false,(0,true),(4,true))] s3_2149 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ffffff00ffffff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons pc34w20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2150 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2150 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_2150 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons pc34w23 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2151 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2151 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false)),(false,(4,true),(0,true))] s3_2151 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xffaaff00ffaaff00ffaaff00ffaaff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons pc34w25 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2152 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2152 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false)),(false,(0,true),(4,true))] s3_2152 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xffaaffaaffaaffaaff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons pc34w26 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2153 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2153 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,false)),(false,(4,true),(0,true))] s3_2153 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w28 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2154 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2154 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(6,true))] s3_2154 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffffffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w30 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2155 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2155 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s3_2155 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff50505050ffffffff50505050,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w33 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2156 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2156 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(4,false)),(false,(6,true),(0,true))] s3_2156 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffaaaa0000ffffffffaaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2157 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2157 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,false)),(false,(0,true),(6,true))] s3_2157 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f00000fffffffff0f00000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w36 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2158 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2158 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,false)),(false,(6,true),(0,true))] s3_2158 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0ffffffff00000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2159 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2159 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,false)),(false,(0,true),(1,true))] s3_2159 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2160 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2160 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true)),(false,(1,true),(3,true))] s3_2160 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w14 rfl)))))))))) (by decide +kernel)
theorem b3_2161 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2161 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_2161 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons pc34w41 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2162 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2162 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,true)),(false,(0,true),(2,true))] s3_2162 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xddddddddddddddddcccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons pc34w44 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2163 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2163 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s3_2163 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w47 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2164 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2164 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,false)),(false,(2,true),(0,true))] s3_2164 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2165 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2165 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_2165 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w9 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2166 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2166 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(0,true),(5,true))] s3_2166 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w52 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2167 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2167 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(0,true),(5,true))] s3_2167 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2168 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2168 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(0,true),(5,true))] s3_2168 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000fffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2169 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2169 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(6,true)),(false,(0,true),(5,true))] s3_2169 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000fffff0f0fffff0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2170 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2170 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_2170 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0a0affff0a0affff0a0affff0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2171 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2171 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_2171 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0a0affff0a0affff0a0affff0a0a,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2172 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2172 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,true)),(false,(0,true),(5,true))] s3_2172 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0f0fffff0f0fffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0fffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w65 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2173 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2173 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,true)),(false,(0,true),(5,true))] s3_2173 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0f0fffff0f0fffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w67 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2174 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2174 := by
  apply PetersenIndexedNode.close (bank := [s4_1620,a4932,s4_0,a4933,a4934,s4_1713,s4_1681,a4935,a4936,s4_1729,s4_1689,a4937,a4938,s4_1731,a4939,s4_1746,s4_1697,a4940,a4941,s4_1733,s4_1705,a4942,a4943,s4_1735,a4944,s4_1727,a4945,s4_1747,s4_1716,a4946,a4947,s4_1745,a4948,a4949,s4_1724,a4950,s4_1726,a4951,a4952,s4_1744]) (PetersenIndexedNode.reasons 256 17 420 0x6222400992000a0208012a4001888900276222280820048a02062224008d8888a0206141280818888c2824222280820044a0208010c0080a001000261411400140402101500031111c180a0005010383014040c444108088406003c21011080c0074c2826141800f98504c283001c108088406003421011080b0a08c2826141800d98504c282c282108088406003028201410280819180a020800cb23009180a02014100a082002c282014104005490804840800b921009081001414100a08191102820141030a08908048406444121009080c28214100a080501048401400084045040280014040a08050102101242008405484806020301280810900a0205212212014048a02003010180a00240602030140045090084808009a12010901001003010180a001c0602030130a098980c4808007b13010980c2820301018084a0a06021280884044c442101128289888420a21010301084045848060203010a0801c140e021612038280c142820030101809444403010180a80810702a020511120e054044a020018080c06001803010180c002c848042408006909008481000a018080c05850403010180b2220848042406141109008480c888018080c04541403010180884044c48210115050989050142101018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c058a8a03020181280810704a02062a2a0e09888aa020018100c0a0010030201814001cc2c06160800498580c2c10006018100c0993120302018130a08c2c0616064c498580c2c0c282018100c084202030210800a0204240210010808848042022808018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c080602212001800181006040300018080c0806020604109001811888850402820280812100a020622224201a080a020282028082000b00048001c0008a080504061412420121010001282014101850450402820400012100908030a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060221201410084800301494100c0484809282212000c04a080030130b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1620 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_35 theta)
    · exact b4_0 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2273 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2272 theta)
    · exact b4_1713 theta
    · exact b4_1681 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_417 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1526 theta)
    · exact b4_1729 theta
    · exact b4_1689 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_527 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1004 theta)
    · exact b4_1731 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1463 theta)
    · exact b4_1746 theta
    · exact b4_1697 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_450 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1541 theta)
    · exact b4_1733 theta
    · exact b4_1705 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_489 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1667 theta)
    · exact b4_1735 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1465 theta)
    · exact b4_1727 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_670 theta)
    · exact b4_1747 theta
    · exact b4_1716 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_587 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1064 theta)
    · exact b4_1745 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_83 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_82 theta)
    · exact b4_1724 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_635 theta)
    · exact b4_1726 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_625 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_530 theta)
    · exact b4_1744 theta
theorem b3_2175 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2175 := by
  apply PetersenIndexedNode.close (bank := [s4_1384,a4953,s4_1678,s4_1683,s4_1415,a4954,s4_1686,s4_1691,s4_1551,a4955,s4_1694,s4_1699,a4956,a4957,s4_1702,s4_1707,a4958,a4959,s4_1711,s4_1718,s4_1619,a4960,s4_1712,s4_1725,a4961,s4_260,s4_1714,s4_1738,s4_1675,a4962,a4963,s4_1692,s4_1676,a4964,a4965,s4_1700,s4_1677,a4966,a4967,s4_1708,s4_1679,a4968,a4969,s4_1719,s4_1680,a4970,a4971,s4_1728,s4_1682,s4_457,a4972,s4_1739,s4_1684,a4973,a4974,s4_1701,s4_1685,a4975,a4976,s4_1709,s4_1687,a4977,a4978,s4_1720,s4_1688,a4979,a4980,s4_1730,s4_1690,s4_586,a4981,s4_1740,s4_1693,a4982,a4983,s4_1710,s4_1695,a4984,a4985,s4_1721,s4_1696,a4986,a4987,s4_1732,s4_1698,s4_869,a4988,s4_1741,s4_1703,a4989,a4990,s4_1722,s4_1704,a4991,a4992,s4_1734,s4_1706,a4993,a4994,s4_1742,s4_1716,a4946,a4995,s4_1736,s4_1717,s4_933,a4996,s4_1743,s4_1723,a4951,a4997,s4_1744]) (PetersenIndexedNode.reasons 256 17 448 0x803731110a00050008036a4001850490008037b111185048444803624000a00050008035280804202a0008034a4001c18090008035a8081c18090208034240004202900080331c08042027000803294000c282500080339c080c282502080321400042025000803126020504098008030a4001918090008031a60219180900880302400050409000802f1602050405800802e9400090805000802f9602090805008802e1400050405000802d0a02090802800802c8840450402800802d8a02050402808802c0840490802101802b250100c049400802aa400109009000802ba501109009004802a240000c0490008029150100c04540080289400189805000802995011898050048028140000c0450008027094140c0425018026884044c4421018027894144c4421058026084040c04210180250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c040602802324808060292008022a4001070290008023a4809070290028022240000602900080211480806025200802094000848050008021948088480500280201400006025000801f0a82806020301801e884044c482101801f8a8284c48280a801e0840406020301801d0a88806020301801c8a08016120b01801d8a88816120309801c0a08006020301801b0180806020600801aa12000c080600801b818080c080602801a2120006020301801924404060491008018a4001070490008019a4405070490018018240000604900080171440406045100801694000c2c05000801794404c2c05001801614000060450008015084040604210080148a020424021008015884044240210180140a020060403028013125040604030280128a08016140b028013925041614030a80120a08006040302801121604060403028010818084a4806028011a16044a48212480100180806040302800f00c0442400300800e8181006040300800f80c0406040301800e0181042400604800d31110a0808404800ca400121009000800db11112100d040800c24000a0809000800b30a0921004202800a94000a0805000800bb0a08a0805040800a1400121005000800918504a0805040800888404e0c02101800998504e0c07040800808404a0802101800712100a080484080068a081311028208007921013110484080060a080a0802820800521200a0805040800481808a88806028005a1200a8885440800401808a0800602800310900a0804240800280c052504030180039090125044240800200c04a0800301800118580a0805040800080c08a2820302800198580a2825140800000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1384 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1377 theta)
    · exact b4_1678 theta
    · exact b4_1683 theta
    · exact b4_1415 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_330 theta)
    · exact b4_1686 theta
    · exact b4_1691 theta
    · exact b4_1551 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1368 theta)
    · exact b4_1694 theta
    · exact b4_1699 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1552 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1369 theta)
    · exact b4_1702 theta
    · exact b4_1707 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1430 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_367 theta)
    · exact b4_1711 theta
    · exact b4_1718 theta
    · exact b4_1619 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_34 theta)
    · exact b4_1712 theta
    · exact b4_1725 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1609 theta)
    · exact b4_260 theta
    · exact b4_1714 theta
    · exact b4_1738 theta
    · exact b4_1675 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_874 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1642 theta)
    · exact b4_1692 theta
    · exact b4_1676 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1556 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1562 theta)
    · exact b4_1700 theta
    · exact b4_1677 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1557 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1561 theta)
    · exact b4_1708 theta
    · exact b4_1679 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_875 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1643 theta)
    · exact b4_1719 theta
    · exact b4_1680 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_458 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1476 theta)
    · exact b4_1728 theta
    · exact b4_1682 theta
    · exact b4_457 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1477 theta)
    · exact b4_1739 theta
    · exact b4_1684 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1634 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_880 theta)
    · exact b4_1701 theta
    · exact b4_1685 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1455 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_462 theta)
    · exact b4_1709 theta
    · exact b4_1687 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_604 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_602 theta)
    · exact b4_1720 theta
    · exact b4_1688 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_934 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_943 theta)
    · exact b4_1730 theta
    · exact b4_1690 theta
    · exact b4_586 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_672 theta)
    · exact b4_1740 theta
    · exact b4_1693 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1388 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1387 theta)
    · exact b4_1710 theta
    · exact b4_1695 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_463 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1454 theta)
    · exact b4_1721 theta
    · exact b4_1696 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_468 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1462 theta)
    · exact b4_1732 theta
    · exact b4_1698 theta
    · exact b4_869 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1627 theta)
    · exact b4_1741 theta
    · exact b4_1703 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_879 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1635 theta)
    · exact b4_1722 theta
    · exact b4_1704 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_870 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1628 theta)
    · exact b4_1734 theta
    · exact b4_1706 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_467 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1464 theta)
    · exact b4_1742 theta
    · exact b4_1716 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_587 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_669 theta)
    · exact b4_1736 theta
    · exact b4_1717 theta
    · exact b4_933 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_944 theta)
    · exact b4_1743 theta
    · exact b4_1723 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_625 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_634 theta)
    · exact b4_1744 theta
theorem b3_2176 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2176 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_2176 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff5050ffff5050ffff5050ffff5050,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff5050ffff5050ffff5050ffff5050,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w70 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w69 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2177 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2177 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_2177 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff5050ffff5050ffff5050ffff5050,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w70 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2178 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2178 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_2178 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff5555ffff5555ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w75 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w73 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2179 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2179 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_2179 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff5555ffff5555ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w75 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2180 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2180 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_2180 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffccccffffcccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w78 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2181 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2181 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(0,true),(5,true))] s3_2181 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w81 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2182 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2182 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(0,true),(5,true))] s3_2182 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2183 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2183 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false)),(false,(0,true),(1,true))] s3_2183 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w86 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w85 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
