import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S13
import Q1020K12L3S20
import Q1020K12L3S21
import Q1020K12L3S23
import Q1020K12L3S26
import Q1020K12L3S37
import Q1020K12L3S40
import Q1020K12L3S41
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S49
import Q1020K12L3S52
import Q1020K12L3S53
import Q1020K12L3S55
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S70
import Q1020K12L3S74
import Q1020K12L3S75
import Q1020K12L3S77
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
import Q1020K12L3S81
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w9 pc26w10 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w10 pc26w12 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa2222222222222222aaaaaaaaaaaaaaaa2222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w10 pc26w14 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w10 pc26w17 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w10 pc26w20 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w22 pc26w10 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 pc26w25 pc26w26 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 pc26w25 pc26w28 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 pc26w25 pc26w30 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w32 pc26w26 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc26w30 pc26w32 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc26w35 pc26w32 rfl rfl







private theorem pc2w43 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w44 : PetersenPackedPin.project cycle2 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w43 stored42 rfl rfl








private theorem pc0w53 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w55 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w54 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w55 stored50 rfl rfl








private theorem pc3w64 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w67 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc26w68 : PetersenPackedPin.project extra26 (0xeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaa : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc26w28 pc26w26 rfl rfl
private theorem pc26w69 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl






private theorem pc30w77 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl

private theorem pc30w76 : PetersenPackedPin.project extra30 (0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w77 stored13 rfl rfl

private theorem pc30w81 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl






private theorem pc32w86 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl

private theorem pc32w90 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl

private theorem pc30w92 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl
private theorem pc26w93 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl




private theorem pc34w98 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc34w97 : PetersenPackedPin.project extra34 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w98 stored19 rfl rfl



private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc2w106 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w107 : PetersenPackedPin.project cycle2 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc2w43 stored42 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w110 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w111 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc2w112 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
theorem b2_420 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_420 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_420 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_421 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_421 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_421 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_422 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_422 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_422 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_423 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_423 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_423 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w15 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_424 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_424 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_424 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_425 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_425 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s2_425 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_426 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_426 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_426 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_427 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_427 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_427 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_428 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_428 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s2_428 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w21 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w23 rfl)))))))))) (by decide +kernel)
theorem b2_429 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_429 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s2_429 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f00000f0f00000f0f0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_430 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_430 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true))] s2_430 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w27 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_431 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_431 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true))] s2_431 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_432 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_432 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true))] s2_432 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_433 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_433 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true))] s2_433 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_434 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_434 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true))] s2_434 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_435 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_435 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_435 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w44 (PetersenWireProjection.cons pc2w43 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_436 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_436 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_436 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w54 (PetersenWireProjection.cons pc0w53 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b2_437 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_437 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s2_437 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w54 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b2_438 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_438 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_438 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_439 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_439 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_439 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons pc3w67 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_440 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_440 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_440 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff00000000000000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w68 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_441 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_441 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_441 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_442 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_442 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_442 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_443 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_443 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_443 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w76 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_444 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_444 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_444 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_445 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_445 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(6,false))] s2_445 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w90 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w86 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_446 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_446 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_446 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w92 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_447 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_447 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_447 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w93 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_448 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_448 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_448 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w98 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w97 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_449 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_449 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_449 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w98 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_450 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_450 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_450 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_451 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_451 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_451 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w43 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w106 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_452 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_452 := by
  apply PetersenIndexedNode.close (bank := [s3_2327,a1776,a1777,a1778,s3_2539,s3_1705,s3_1704,s3_1702,a1779,a1780,a1781,s3_2791,a1782,a1783,a1784,a1785,a1786,a1787,a1788,a1789,a1790,a1791,a1792,a1793,s3_1840,a1794,a1795,a1796,a1797,a1798,s3_2829,a1799,a1800,s3_2758,a1801,s3_2756,s3_1710,s3_1709,s3_1708,a1802,a1803,a1804,a1805,a1806,s3_2792,a1807,a1808,a1809,a1810,a1811,s3_571,a1812,a1813,a1814,a1815,a1816,s3_1711,a1817,s3_2794,a1818,s3_1716,a1819,s3_2797,a1820,a1821,a1822,a1823,a1824,s3_1718,s3_2068,s3_2798,a1825,a1826,a1827,a1828,s3_9,a1829,a1830,a1831,a1832,a1833,s3_2784]) (PetersenIndexedNode.reasons 256 17 510 0x2009e4202210121012009a84048028c01410889004f8027311110809004b4202401360098c28221014012c8404a0201080a80010808a0805000280814100a0204202084044202622210808840484046141308098888c2826222210108404420300491080884060090e0c0706040129c180e0c08023884044202901028202400108089080480024041210090104202141010808501048401400084045040280014040a0805010210124200840500452820141020088d0c0686040119a180d0c0802194100a080311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a08108084808141012000840448402400120209080480821010a0808405004114100a0820080c8c06460401099180c8c0801f8a0805040280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018088404c4c02101130318980480c2101018080c05003d03010180a0078c4c06260400f98980c4c0801d818080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c049212018080c05080883814180a484907029012420200c04060242020180908009010424021001080884804202240400c0406030039018080c060070c2c06160400e98580c2c0801b80c0406030020018080c044203000e1080c00da006a280a494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203015111400cd4444840480192101144450034511121012006284043111400bcc4444202801710808c445003031111080a005a42028014c00a2004f00268012c00920059002b80154008e0045002180104007c541421018006084060037001a800c9410200305040800f4007600385040800b941005445001515110a082002828201511400585444282080098a0804c45001113110180a002006021311400484c44060280078180a001d000d131200c0600180301428280c080604840441c120c090a0a83824202a101006040302248480c080604420230b0108089212616024049080806040302800400c08060500078003400160017000a8004c001006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c0806050001119108c8a0006232211914000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2327 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1718 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2068 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2798 theta)
    · exact b3_2539 theta
    · exact b3_1705 theta
    · exact b3_1704 theta
    · exact b3_1702 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1840 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2969 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2829 theta)
    · exact b3_2791 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_9 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_918 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_850 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2332 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1846 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1716 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2797 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2332 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1846 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1716 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2797 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2539 theta)
    · exact b3_1840 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1705 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1702 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1704 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2969 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2791 theta)
    · exact b3_2829 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_918 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_850 theta)
    · exact b3_2758 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2756 theta)
    · exact b3_2756 theta
    · exact b3_1710 theta
    · exact b3_1709 theta
    · exact b3_1708 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1710 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1708 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1709 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3244 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2792 theta)
    · exact b3_2792 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2759 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_571 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1711 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2794 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2759 theta)
    · exact b3_571 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1711 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2794 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2784 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2784 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2759 theta)
    · exact b3_1711 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_571 theta)
    · exact b3_2794 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2332 theta)
    · exact b3_1716 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1846 theta)
    · exact b3_2797 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2332 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1716 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1846 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2797 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2327 theta)
    · exact b3_1718 theta
    · exact b3_2068 theta
    · exact b3_2798 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2759 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1711 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_571 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2794 theta)
    · exact b3_9 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_918 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_850 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_918 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_850 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2784 theta)
    · exact b3_2784 theta
theorem b2_453 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_453 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_453 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w30 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_454 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_454 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_454 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w43 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w107 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_455 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_455 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_455 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w108 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b2_456 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_456 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_456 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w109 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_457 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_457 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(0,false))] s2_457 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w90 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w110 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b2_458 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_458 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_458 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w98 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w111 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_459 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_459 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_459 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w43 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w112 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b2_460 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_460 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s2_460 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w43 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b2_461 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_461 := by
  apply PetersenIndexedNode.close (bank := [s3_2328,a1834,a1835,s3_3109,s3_2695,s3_53,a1836,s3_2804,a764,a1837,a1838,a1839,a1840,a1841,a1842,a1843,a1844,a1845,a1846,a1847,s3_1841,a1848,a1849,a1850,s3_3437,a1851,s3_2831,a1852,a1853,a1854,a1855,a1856,a1857,a1858,a1859,a1860,a1861,a1862,s3_580,a1863,a1864,a1865,s3_3382,a1866,s3_2809,s3_2768,s3_2769,s3_2767,s3_68,s3_69,s3_67,a1867,a1868,a1869,a1870,a1871,s3_2805,a1872,s3_2827,a1873,s3_2811,s3_2773,s3_109,a1874,s3_2806,a1875,a1876,a1877,s3_167,a1878,s3_2807,a1879,s3_2812,a1880,a1881,a1882,a1883,s3_2082,a1884,a1885,s3_2813,a1886,a1887,a1888,s3_186,s3_2243,s3_2244,s3_2242,s3_2808,a1889,a1890,a1891,a1892,a1893,a1894,a1833,s3_2784,a1895,a1896,s3_9,a1831,a1829]) (PetersenIndexedNode.reasons 256 17 510 0x200cb006142024018d8888840480324018884050063614110809888900626222401858504c28280304017d0889005d10808840600b8614130a0c0178c2826141802d884044202e0601080884058888a0807020381814100e060622208404420300591080884058504614130a0c0168c282614161410840442030057802b4015600a85040282040160a08050408029c014a00a3004f2820141018888908068204014121009080622214100a081004d48402420185045040282040138a08050406141242012100311128200c4044202706010808c444e0c021111080941004203004b14100a082009448402420401309080484080248a0805041004714100a0818888c8c0642040121918048c062220a0805040c88814100a081850448402420322209080484061410a0805040280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805041004503010180a00888480424040119090084808021818080c04c444030101809c0c084806220311110900c4447030018080c0500410301018098504c4c0624040109898084c06141018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c05003f018080c06007c424021204010084804240801e80c040603003b018080c05888883816120400f107028381622200c040602c282018080c0591104240212030a0884804240644400c040603001c018080c044203000a1080c00ea0072280a494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301801ac00d2006700328018c00c200710037801b400be005d002d8014c00a2004ec4448013311120059002b801531112004ac4448010c0082003ec282800f30a0a00490023801130a0a003ac282800e4006c54142101800408406002f0016800a9410200285040800d40066003050408009941005445001115110a082002028201511400485444282080078a0804c45000d13110180a001806021311400384c44060280058180a00150009131200c0600100301800300c080605000530b018582000e616030b0400100604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c0806050001119108c8a0006232211914000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2328 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1719 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2069 theta)
    · exact b3_3109 theta
    · exact b3_2695 theta
    · exact b3_53 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2060 theta)
    · exact b3_2804 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_18 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_973 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_851 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2333 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1847 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1717 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3112 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2333 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1847 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1717 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3112 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2540 theta)
    · exact b3_1841 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1707 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1703 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1706 theta)
    · exact b3_3437 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3190 theta)
    · exact b3_2831 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_973 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_851 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2761 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_580 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1714 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1712 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1713 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3382 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3253 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2809 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2761 theta)
    · exact b3_580 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1714 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1712 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1713 theta)
    · exact b3_3382 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_3253 theta)
    · exact b3_2809 theta
    · exact b3_2768 theta
    · exact b3_2769 theta
    · exact b3_2767 theta
    · exact b3_68 theta
    · exact b3_69 theta
    · exact b3_67 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1723 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1721 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1722 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3347 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3280 theta)
    · exact b3_2805 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2827 theta)
    · exact b3_2827 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1114 theta)
    · exact b3_2811 theta
    · exact b3_2773 theta
    · exact b3_109 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1576 theta)
    · exact b3_2806 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1926 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2812 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2667 theta)
    · exact b3_167 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2205 theta)
    · exact b3_2807 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_1926 theta)
    · exact b3_2812 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2667 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_167 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2205 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2807 theta)
    · exact b3_2082 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2813 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2082 theta)
    · exact b3_2813 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2530 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2524 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2515 theta)
    · exact b3_186 theta
    · exact b3_2243 theta
    · exact b3_2244 theta
    · exact b3_2242 theta
    · exact b3_2808 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1114 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2811 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2773 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_109 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1576 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2806 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2784 theta)
    · exact b3_2784 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_919 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_919 theta)
    · exact b3_9 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_918 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_918 theta)
end Orbits1020Cost12
