import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc26w8 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored6 stored7 rfl rfl
private theorem pc26w7 : PetersenPackedPin.project extra26 (0x5555555544444444555555554444444455555555444444445555555544444444 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w8 pc26w9 rfl rfl

private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w11 pc26w13 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0x8888000088880000888800008888000088880000888800008888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w10 pc26w15 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0x8888888800000000888888880000000088888888000000008888888800000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w15 stored2 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w18 pc26w15 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w21 stored0 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0x888888888888888888888888888888888888888888888888aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w20 pc26w15 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0x88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w23 pc26w15 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w18 pc26w26 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0x8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w25 pc26w15 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored3 stored7 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w20 pc26w29 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0x33333333333333330000000000000000 := PetersenWireProjection.derive 1 stored2 stored3 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xffff000000000000ffff000000000000ffff000000000000000000000000 : BitVec 256) = 0x32323232323232320000000000000000 := PetersenWireProjection.derive 0 pc26w18 pc26w32 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w31 stored7 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored3 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0x333300003333000033330000333300003333000033330000000000000000 : BitVec 256) = 0x3232000032320000323200003232 := PetersenWireProjection.derive 1 pc26w18 pc26w35 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xaaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaa8888aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc26w34 stored7 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w37 pc26w15 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w39 pc26w23 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa2222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w39 pc26w42 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w39 pc26w15 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w39 pc26w37 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w40 pc26w46 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w43 pc26w46 rfl rfl
private theorem pc26w50 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 pc26w50 pc26w51 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0x5050000050500000505000005050000 := PetersenWireProjection.derive 1 pc26w49 pc26w52 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 pc26w52 pc26w51 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w54 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 pc26w52 pc26w55 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w57 : PetersenPackedPin.project extra26 (0xffff000000000000ffff000000000000ffff0000000000000000 : BitVec 256) = 0x3232323232323232 := PetersenWireProjection.derive 1 pc26w18 pc26w58 rfl rfl
private theorem pc26w56 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x3232323232323232 := PetersenWireProjection.derive 3 pc26w57 stored7 rfl rfl
private theorem pc26w59 : PetersenPackedPin.project extra26 (0xaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w8 pc26w51 rfl rfl
private theorem pc26w62 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w61 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w62 stored0 rfl rfl
private theorem pc26w60 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc26w61 pc26w8 rfl rfl
private theorem pc26w65 : PetersenPackedPin.project extra26 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0x33330000333300003333000033330000 := PetersenWireProjection.derive 2 stored3 stored6 rfl rfl
private theorem pc26w64 : PetersenPackedPin.project extra26 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000000000000000 : BitVec 256) = 0x32320000323200003232000032320000 := PetersenWireProjection.derive 0 pc26w18 pc26w65 rfl rfl
private theorem pc26w63 : PetersenPackedPin.project extra26 (0xaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0x32320000323200003232000032320000 := PetersenWireProjection.derive 3 pc26w64 stored7 rfl rfl
private theorem pc26w67 : PetersenPackedPin.project extra26 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 1 stored3 stored7 rfl rfl
private theorem pc26w66 : PetersenPackedPin.project extra26 (0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 1 pc26w61 pc26w67 rfl rfl







private theorem pc30w76 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w78 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w75 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w76 pc30w78 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl
private theorem pc30w74 : PetersenPackedPin.project extra30 (0xc0c00000c0c00000c0c00000c0c00000c0c00000c0c00000c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w75 pc30w79 rfl rfl

private theorem pc30w81 : PetersenPackedPin.project extra30 (0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w79 stored10 rfl rfl
private theorem pc30w83 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w82 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w83 pc30w79 rfl rfl
private theorem pc30w86 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w85 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w86 stored13 rfl rfl
private theorem pc30w87 : PetersenPackedPin.project extra30 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff00000000 := PetersenWireProjection.derive 1 stored8 stored14 rfl rfl
private theorem pc30w84 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w85 pc30w87 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa := PetersenWireProjection.derive 1 stored10 stored14 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xc0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc30w89 stored13 rfl rfl
private theorem pc30w92 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w91 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffffffff0fff0fffffffffff0fff0 := PetersenWireProjection.derive 3 pc30w92 stored8 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0xff00ff00ff00ff0000000000000000 := PetersenWireProjection.derive 1 stored11 stored14 rfl rfl
private theorem pc30w90 : PetersenPackedPin.project extra30 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xff00ff00ff00ff00fffffffffff0fff0 := PetersenWireProjection.derive 1 pc30w91 pc30w93 rfl rfl
private theorem pc30w96 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored11 stored13 rfl rfl
private theorem pc30w95 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w83 pc30w96 rfl rfl
private theorem pc30w94 : PetersenPackedPin.project extra30 (0xc0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w95 pc30w79 rfl rfl
theorem b4_1848 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1848 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,true),(8,true))] s4_1848 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0xffffffffffffffffffff0000ffff0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w7 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1849 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1849 := by
  apply node_sound (nxt := [s5_31])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    subst R
    exact b5_31 theta
theorem b4_1850 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1850 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_1851 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1851 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1851 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1852 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1852 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1852 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1853 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1853 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1853 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1854 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1854 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1854 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1855 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1855 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1855 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1856 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1856 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1856 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1857 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1857 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1857 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1858 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1858 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1858 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1859 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1859 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1859 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1860 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1860 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_1860 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w30 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1861 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1861 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1861 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1862 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1862 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1862 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1863 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1863 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(6,true),(8,true))] s4_1863 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1864 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1864 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1864 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))) (by decide +kernel)
theorem b4_1865 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1865 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1865 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w18 rfl))))))))) (by decide +kernel)
theorem b4_1866 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1866 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1866 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1867 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1867 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_1867 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1868 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1868 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_1868 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w41 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1869 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1869 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1869 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1870 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1870 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_1870 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1871 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1871 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true))] s4_1871 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w45 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1872 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1872 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s4_1872 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons pc26w47 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1873 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1873 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(0,false),(5,false)),(false,(3,true),(1,true))] s4_1873 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x5050000050500000505000005050000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w48 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1874 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1874 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(1,true),(3,true)),(false,(3,true),(0,true))] s4_1874 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xf0f00000f0f00000f0f00000f0f0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1875 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1875 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(1,true),(3,true)),(false,(3,true),(0,true))] s4_1875 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xf0f0f0f0f0f0f0f0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1876 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1876 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(2,true),(0,true)),(false,(0,false),(8,true))] s4_1876 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x3232323232323232,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w56 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1877 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1877 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,true),(1,true)),(false,(3,true),(0,true))] s4_1877 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w59 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1878 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1878 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(0,true),(7,true)),(false,(3,true),(1,true))] s4_1878 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xfafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w60 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1879 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1879 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(0,false),(6,false))] s4_1879 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x32320000323200003232000032320000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w63 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1880 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1880 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(3,true)),(false,(3,true),(0,true))] s4_1880 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0x32323232323232323232323232323232,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w10 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w66 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_1881 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1881 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1881 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w74 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1882 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1882 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1882 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1883 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1883 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1883 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w82 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1884 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1884 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(6,true)),(false,(8,true),(0,true))] s4_1884 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1885 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1885 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1885 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w84 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1886 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1886 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1886 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1887 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1887 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1887 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))) (by decide +kernel)
theorem b4_1888 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1888 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true)),(false,(0,true),(5,true))] s4_1888 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00fffffffffff0fff0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w90 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_1889 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_1889 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s4_1889 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
