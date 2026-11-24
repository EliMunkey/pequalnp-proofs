import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0x333333333333333300000000000000000000000000000000 : BitVec 256) = 0x5050000050500000505000005050 := PetersenWireProjection.derive 2 pc26w10 stored0 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w12 pc26w13 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa888888888888888888888888aaaaaaaa88888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w9 pc26w11 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored0 stored1 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa000000000000000088888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w11 pc26w15 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0x33333333333333330000000000000000 : BitVec 256) = 0xa0a00000a0a00000a0a00000a0a := PetersenWireProjection.derive 1 pc26w18 stored0 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa888888888888888888888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w17 pc26w11 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w11 pc26w20 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w10 stored0 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w22 pc26w11 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 pc26w24 pc26w25 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored4 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 1 stored1 stored4 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 1 pc26w27 pc26w28 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored0 stored5 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored1 stored5 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 2 pc26w30 pc26w31 rfl rfl








private theorem pc22w40 : PetersenPackedPin.project tree22 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored273 stored280 rfl rfl
private theorem pc22w42 : PetersenPackedPin.project tree22 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored279 stored280 rfl rfl
private theorem pc22w39 : PetersenPackedPin.project tree22 (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc22w40 pc22w42 rfl rfl
private theorem pc22w45 : PetersenPackedPin.project tree22 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored275 stored279 rfl rfl
private theorem pc22w44 : PetersenPackedPin.project tree22 (0x33333333000000003333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc22w45 stored273 rfl rfl
private theorem pc22w47 : PetersenPackedPin.project tree22 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored275 stored280 rfl rfl
private theorem pc22w48 : PetersenPackedPin.project tree22 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored279 stored280 rfl rfl
private theorem pc22w46 : PetersenPackedPin.project tree22 (0x88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc22w47 pc22w48 rfl rfl
private theorem pc22w43 : PetersenPackedPin.project tree22 (0x88888888bbbbbbbb88888888bbbbbbbb88888888aaaaaaaa88888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc22w44 pc22w46 rfl rfl








private theorem pc1w57 : PetersenPackedPin.project cycle1 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored58 stored64 rfl rfl
private theorem pc1w59 : PetersenPackedPin.project cycle1 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored59 stored64 rfl rfl
private theorem pc1w56 : PetersenPackedPin.project cycle1 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 1 pc1w57 pc1w59 rfl rfl
private theorem pc1w61 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl
private theorem pc1w60 : PetersenPackedPin.project cycle1 (0x88888888cccccccc888888888888888800000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w56 pc1w61 rfl rfl








private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored40 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored40 rfl rfl
private theorem pc3w69 : PetersenPackedPin.project cycle3 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 pc3w70 pc3w72 rfl rfl
private theorem pc3w74 : PetersenPackedPin.project cycle3 (0x88888888cccccccc88888888cccccccc88888888cccccccc88888888cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc3w72 stored39 rfl rfl
private theorem pc3w73 : PetersenPackedPin.project cycle3 (0x88888888cccccccc888888888888888888888888cccccccc8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w74 pc3w70 rfl rfl






private theorem pc23w82 : PetersenPackedPin.project tree23 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored82 stored83 rfl rfl


private theorem pc23w83 : PetersenPackedPin.project tree23 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 stored87 stored88 rfl rfl
private theorem pc23w81 : PetersenPackedPin.project tree23 (0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 3 pc23w82 pc23w83 rfl rfl
private theorem pc23w87 : PetersenPackedPin.project tree23 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored82 stored88 rfl rfl
private theorem pc23w88 : PetersenPackedPin.project tree23 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored83 stored88 rfl rfl
private theorem pc23w86 : PetersenPackedPin.project tree23 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc23w87 pc23w88 rfl rfl
private theorem pc23w90 : PetersenPackedPin.project tree23 (0x88888888cccccccc88888888cccccccc88888888cccccccc88888888cccccccc : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 2 pc23w88 stored87 rfl rfl
private theorem pc23w89 : PetersenPackedPin.project tree23 (0x88888888cccccccc888888888888888888888888cccccccc8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc23w90 pc23w87 rfl rfl
private theorem pc23w91 : PetersenPackedPin.project tree23 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffccccffffcccc := PetersenWireProjection.derive 3 stored81 stored87 rfl rfl
private theorem pc3w93 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored34 stored35 rfl rfl
private theorem pc3w94 : PetersenPackedPin.project cycle3 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored39 stored40 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 3 pc3w93 pc3w94 rfl rfl
private theorem pc23w96 : PetersenPackedPin.project tree23 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored81 stored88 rfl rfl
private theorem pc23w95 : PetersenPackedPin.project tree23 (0xffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 pc23w96 pc23w82 rfl rfl
private theorem pc23w98 : PetersenPackedPin.project tree23 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xcccc0000cccc := PetersenWireProjection.derive 1 stored81 stored87 rfl rfl
private theorem pc23w97 : PetersenPackedPin.project tree23 (0x88888888cccccccc8888888888888888aaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc23w86 pc23w98 rfl rfl
private theorem pc3w101 : PetersenPackedPin.project cycle3 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored40 rfl rfl
private theorem pc3w100 : PetersenPackedPin.project cycle3 (0x5555555500000000555555555555555500000000000000000000000000000000 : BitVec 256) = 0xc0c0f0f0 := PetersenWireProjection.derive 1 pc3w101 pc3w93 rfl rfl
private theorem pc3w99 : PetersenPackedPin.project cycle3 (0x88888888cccccccc8888888888888888cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc3w100 stored39 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored40 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored39 stored40 rfl rfl
private theorem pc3w102 : PetersenPackedPin.project cycle3 (0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 pc3w103 pc3w104 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w108 stored0 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl
private theorem pc26w106 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0aaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w107 pc26w109 rfl rfl
private theorem pc26w105 : PetersenPackedPin.project extra26 (0xa0a0a0a0aaaaaaaaa0a0a0a0aaaaaaaaaaaaaaaaaaaaaaaaa0a0a0a0aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w106 pc26w12 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xff00ffffff00ffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 pc26w111 stored5 rfl rfl
private theorem pc26w113 : PetersenPackedPin.project extra26 (0xc0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0000000f0000000f000f000f000f0 := PetersenWireProjection.derive 1 pc26w30 pc26w111 rfl rfl
private theorem pc26w112 : PetersenPackedPin.project extra26 (0xa2a2a2a2a0a0a0a0a2a2a2a2a0a0a0a0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w113 stored7 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xa2a2a2a2a0a0a0a0a2a2a2a2a0a0a0a0a2a2a2a2a0a0a0a0a2a2a2a2a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w110 stored7 rfl rfl
private theorem pc26w116 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w114 : PetersenPackedPin.project extra26 (0xa2a2a2a2a0a0a0a0aaaaaaaaaaaaaaaaa2a2a2a2a0a0a0a0aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w115 pc26w116 rfl rfl
private theorem pc26w119 : PetersenPackedPin.project extra26 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 2 stored5 stored6 rfl rfl
private theorem pc26w118 : PetersenPackedPin.project extra26 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c : BitVec 256) = 0xf5000000f5000000f5000000f50000 := PetersenWireProjection.derive 2 pc26w15 pc26w119 rfl rfl
private theorem pc26w117 : PetersenPackedPin.project extra26 (0xa2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2aaaaaaaaaaaaaaaaa2a2a2a2a2a2a2a2 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w118 stored7 rfl rfl
private theorem pc26w122 : PetersenPackedPin.project extra26 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffffff00ffffff00ffffff00ffffff00 := PetersenWireProjection.derive 3 stored5 stored6 rfl rfl
private theorem pc26w121 : PetersenPackedPin.project extra26 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xffffff0affffff0affffff0affffff0a := PetersenWireProjection.derive 3 pc26w15 pc26w122 rfl rfl
private theorem pc26w120 : PetersenPackedPin.project extra26 (0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w121 stored7 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f00000fffffffff0f00000 := PetersenWireProjection.derive 3 pc26w124 stored4 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888800000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w13 stored0 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored4 stored7 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xaa88aa88aa88aa88aa88aa88aa88aa88aa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w127 pc26w128 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xaa88aa88aa88aa88aaaaaaaaaaaaaaaaaa00aa00aa00aa00aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w126 pc26w116 rfl rfl
private theorem pc26w131 : PetersenPackedPin.project extra26 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x50505050505050505050505050505050 := PetersenWireProjection.derive 1 stored0 stored1 rfl rfl
private theorem pc26w132 : PetersenPackedPin.project extra26 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xffffffffffff0000ffffffffffff0000 := PetersenWireProjection.derive 3 stored4 stored6 rfl rfl
private theorem pc26w130 : PetersenPackedPin.project extra26 (0xffccffccffccffccffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xffffffffffff5050ffffffffffff5050 := PetersenWireProjection.derive 3 pc26w131 pc26w132 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xaa88aa88aa88aa88aaaaaaaaaaaaaaaaaa88aa88aa88aa88aa88aa88aa88aa88 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w130 stored7 rfl rfl
private theorem pc26w133 : PetersenPackedPin.project extra26 (0xaa88aa88aaaaaaaaaa88aa88aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w126 pc26w12 rfl rfl
private theorem pc26w135 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w136 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w134 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xddddddddddddddddcccccccccccccccc := PetersenWireProjection.derive 2 pc26w135 pc26w136 rfl rfl
private theorem pc26w139 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w140 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w138 : PetersenPackedPin.project extra26 (0xffff0000ffff000000000000ffff00000000000000000000000000000000 : BitVec 256) = 0x20202020202020203030303030303030 := PetersenWireProjection.derive 1 pc26w139 pc26w140 rfl rfl
private theorem pc26w137 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w138 stored7 rfl rfl
private theorem pc26w142 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w141 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w142 stored3 rfl rfl
private theorem pc26w145 : PetersenPackedPin.project extra26 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0x33333333333333330000000000000000 := PetersenWireProjection.derive 1 stored2 stored3 rfl rfl
private theorem pc26w144 : PetersenPackedPin.project extra26 (0xffff000000000000ffff0000000000003333000000000000333300000000 : BitVec 256) = 0x30303333303033330000000000000000 := PetersenWireProjection.derive 2 pc26w142 pc26w145 rfl rfl
private theorem pc26w143 : PetersenPackedPin.project extra26 (0xaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa8888aaaaaaaaaaaa8888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w144 stored7 rfl rfl
private theorem pc26w147 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w146 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w147 stored3 rfl rfl
private theorem pc26w149 : PetersenPackedPin.project extra26 (0x33330000ffff000033330000ffff00000000000000000000000000000000 : BitVec 256) = 0x3030000030303030303030303030 := PetersenWireProjection.derive 1 pc26w139 pc26w147 rfl rfl
private theorem pc26w148 : PetersenPackedPin.project extra26 (0xaaaa8888aaaa0000aaaa8888aaaa0000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w149 stored7 rfl rfl
private theorem pc26w152 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored3 stored6 rfl rfl
private theorem pc26w151 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffffffffffccccffffccccffffccccffffffffffffcccc : BitVec 256) = 0xffffddddffffddddffffccccffffcccc := PetersenWireProjection.derive 3 pc26w140 pc26w152 rfl rfl
private theorem pc26w150 : PetersenPackedPin.project extra26 (0xaaaa8888aaaa8888aaaaaaaaaaaa8888aaaa8888aaaa8888aaaaaaaaaaaa8888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w151 stored7 rfl rfl
private theorem pc26w154 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w155 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w153 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0ffff0000ffff0000 := PetersenWireProjection.derive 0 pc26w154 pc26w155 rfl rfl
private theorem pc26w157 : PetersenPackedPin.project extra26 (0xaaaaaaaa888888880000000000000000aaaaaaaa888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w108 pc26w155 rfl rfl
private theorem pc26w156 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888000000000000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w157 pc26w154 rfl rfl
private theorem pc26w160 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w159 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w160 pc26w13 rfl rfl
private theorem pc26w158 : PetersenPackedPin.project extra26 (0xaaaaaaaa888888880000000000000000aaaaaaaa88888888aaaaaaaa88888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w159 pc26w131 rfl rfl
private theorem pc26w162 : PetersenPackedPin.project extra26 (0xaaaaaaaa000000000000000000000000aaaaaaaa000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w160 stored1 rfl rfl
private theorem pc26w161 : PetersenPackedPin.project extra26 (0xaaaaaaaa888888888888888888888888aaaaaaaa000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w162 pc26w127 rfl rfl
private theorem pc26w164 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w160 stored0 rfl rfl
private theorem pc26w165 : PetersenPackedPin.project extra26 (0x8888888888888888000000000000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w13 stored1 rfl rfl
private theorem pc26w163 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa0000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w164 pc26w165 rfl rfl
private theorem pc26w167 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w166 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w167 stored2 rfl rfl
private theorem pc26w169 : PetersenPackedPin.project extra26 (0x3333333300000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x5050f0f05050f0f0 := PetersenWireProjection.derive 1 pc26w24 pc26w167 rfl rfl
private theorem pc26w168 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w169 stored7 rfl rfl
private theorem pc26w170 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w159 pc26w20 rfl rfl
private theorem pc26w172 : PetersenPackedPin.project extra26 (0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc : BitVec 256) = 0xffffffffffffffffffffffffffff0000 := PetersenWireProjection.derive 3 pc26w132 stored2 rfl rfl
private theorem pc26w171 : PetersenPackedPin.project extra26 (0xffffffffffccffccffffffffffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f00000 := PetersenWireProjection.derive 0 pc26w172 pc26w27 rfl rfl
theorem b4_2310 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2310 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2310 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2311 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2311 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2311 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2312 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2312 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2312 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2313 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2313 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2313 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2314 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2314 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2314 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2315 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2315 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(7,true))] s4_2315 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2316 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2316 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s4_2316 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2317 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2317 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s4_2317 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2318 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2318 := by
  intro m le c
  apply rejects_sound tree22 i6 6 tgt small22 hot22 [] s4_2318 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0xffffffff00000000,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0] (PetersenWireProjection.cons pc22w43 (PetersenWireProjection.cons pc22w39 (PetersenWireProjection.cons stored279 (PetersenWireProjection.cons stored278 (PetersenWireProjection.cons stored277 (PetersenWireProjection.cons stored276 (PetersenWireProjection.cons stored275 (PetersenWireProjection.cons stored274 (PetersenWireProjection.cons stored273 rfl))))))))) (by decide +kernel)
theorem b4_2319 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2319 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2319 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaafafa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w60 (PetersenWireProjection.cons pc1w56 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b4_2320 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2320 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(1,true))] s4_2320 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x33330000,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w73 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2321 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2321 := by
  intro m le c
  apply rejects_sound tree23 i6 6 tgt small23 hot23 [] s4_2321 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc23w89 (PetersenWireProjection.cons pc23w86 (PetersenWireProjection.cons pc23w81 (PetersenWireProjection.cons stored86 (PetersenWireProjection.cons stored85 (PetersenWireProjection.cons stored84 (PetersenWireProjection.cons stored83 (PetersenWireProjection.cons stored82 (PetersenWireProjection.cons stored81 rfl))))))))) (by decide +kernel)
theorem b4_2322 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2322 := by
  intro m le c
  apply rejects_sound tree23 i6 6 tgt small23 hot23 [(false,(1,true),(4,true))] s4_2322 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc,0xffffccccffffcccc] (PetersenWireProjection.cons pc23w89 (PetersenWireProjection.cons pc23w86 (PetersenWireProjection.cons stored86 (PetersenWireProjection.cons stored85 (PetersenWireProjection.cons stored84 (PetersenWireProjection.cons stored83 (PetersenWireProjection.cons stored82 (PetersenWireProjection.cons stored81 (PetersenWireProjection.cons pc23w91 rfl))))))))) (by decide +kernel)
theorem b4_2323 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2323 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(1,true))] s4_2323 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x33330000,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w73 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2324 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2324 := by
  intro m le c
  apply rejects_sound tree23 i6 6 tgt small23 hot23 [] s4_2324 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc,0xcccccccccccccccc] (PetersenWireProjection.cons pc23w89 (PetersenWireProjection.cons stored87 (PetersenWireProjection.cons stored86 (PetersenWireProjection.cons stored85 (PetersenWireProjection.cons stored84 (PetersenWireProjection.cons stored83 (PetersenWireProjection.cons stored82 (PetersenWireProjection.cons stored81 (PetersenWireProjection.cons pc23w95 rfl))))))))) (by decide +kernel)
theorem b4_2325 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2325 := by
  intro m le c
  apply rejects_sound tree23 i6 6 tgt small23 hot23 [] s4_2325 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc23w97 (PetersenWireProjection.cons pc23w86 (PetersenWireProjection.cons stored87 (PetersenWireProjection.cons stored86 (PetersenWireProjection.cons stored85 (PetersenWireProjection.cons stored84 (PetersenWireProjection.cons stored83 (PetersenWireProjection.cons stored82 (PetersenWireProjection.cons stored81 rfl))))))))) (by decide +kernel)
theorem b4_2326 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2326 := by
  intro m le c
  apply rejects_sound tree23 i6 6 tgt small23 hot23 [] s4_2326 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc23w97 (PetersenWireProjection.cons stored87 (PetersenWireProjection.cons stored86 (PetersenWireProjection.cons stored85 (PetersenWireProjection.cons stored84 (PetersenWireProjection.cons stored83 (PetersenWireProjection.cons stored82 (PetersenWireProjection.cons stored81 rfl)))))))) (by decide +kernel)
theorem b4_2327 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2327 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(1,true))] s4_2327 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x33330000,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w99 (PetersenWireProjection.cons pc3w69 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2328 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2328 := by
  apply node_sound (nxt := [a6618,s5_36,a6619,s5_35,s5_5,s5_37])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b5_19 theta)
    · exact b5_36 theta
    · exact via sym7 fix7 (by decide +kernel) (b5_20 theta)
    · exact b5_35 theta
    · exact b5_5 theta
    · exact b5_37 theta
theorem b4_2329 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2329 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2329 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons pc3w102 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2330 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2330 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s4_2330 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w105 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2331 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2331 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true)),(false,(0,true),(4,true))] s4_2331 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ffffff00ffffff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w112 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2332 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2332 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true)),(false,(0,true),(4,true))] s4_2332 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ffffff00ffffff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w114 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2333 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2333 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,true)),(false,(0,true),(4,true))] s4_2333 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ffffff00ffffff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w114 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))) (by decide +kernel)
theorem b4_2334 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2334 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s4_2334 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w117 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2335 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2335 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s4_2335 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w120 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2336 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2336 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false)),(false,(0,true),(6,true))] s4_2336 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffff0f00000fffffffff0f00000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w125 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w123 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2337 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2337 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s4_2337 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2338 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2338 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,false)),(false,(0,true),(6,true))] s4_2338 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffff0f00000fffffffff0f00000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w133 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w123 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2339 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2339 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(2,true))] s4_2339 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xddddddddddddddddcccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w137 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w134 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2340 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2340 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s4_2340 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w143 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w141 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2341 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2341 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(4,false)),(false,(0,true),(2,true))] s4_2341 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w148 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w146 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2342 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2342 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(2,true))] s4_2342 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xddddddddddddddddcccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w150 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w134 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2343 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2343 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,true))] s4_2343 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffff0f0fffff0f0ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w156 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w153 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2344 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2344 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2344 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w158 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2345 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2345 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2345 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w161 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2346 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2346 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2346 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w163 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2347 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2347 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s4_2347 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w168 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w166 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2348 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2348 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s4_2348 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w170 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2349 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2349 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(7,true))] s4_2349 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w159 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2350 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2350 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true))] s4_2350 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w159 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2351 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2351 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,false)),(false,(0,true),(7,true))] s4_2351 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffffffff0f0f0f0fffffffff0f00000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w159 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w171 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
