import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S27
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S41
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S44
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S48
import Q1020K12L4S49
import Q1020K12L4S56
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0






private theorem pc26w4 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl


private theorem pc26w9 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored0 stored3 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 3 pc26w9 pc26w11 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl






private theorem pc30w17 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl


private theorem pc30w22 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w24 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w21 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w22 pc30w24 rfl rfl
private theorem pc30w25 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl





private theorem pc32w29 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl



private theorem pc32w35 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w37 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w34 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc32w35 pc32w37 rfl rfl
private theorem pc32w38 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc30w39 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl




private theorem pc34w43 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored17 stored19 rfl rfl




private theorem pc34w50 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w51 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w49 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w50 pc34w51 rfl rfl
private theorem pc34w52 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w54 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored16 stored19 rfl rfl
private theorem pc34w53 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc34w54 pc34w43 rfl rfl
private theorem pc34w55 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w56 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w58 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w56 stored16 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl


private theorem pc0w62 : PetersenPackedPin.project cycle0 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored49 stored50 rfl rfl






private theorem pc0w69 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 stored49 stored52 rfl rfl
private theorem pc0w71 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w68 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w69 pc0w71 rfl rfl
private theorem pc0w72 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc34w73 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000ffff0000ffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w50 stored17 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl


private theorem pc39w75 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl

private theorem pc39w78 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl





private theorem pc39w85 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w87 : PetersenPackedPin.project extra39 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored74 stored76 rfl rfl
private theorem pc39w84 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w85 pc39w87 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc32w89 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc39w90 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored75 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w74 stored0 rfl rfl
private theorem pc39w92 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w78 stored73 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w88 stored8 rfl rfl
theorem b3_2268 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2268 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2268 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w4 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2269 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2269 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2269 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w4 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2270 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2270 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2270 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w17 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2271 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2271 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2271 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w17 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w25 rfl)))))))))) (by decide +kernel)
theorem b3_2272 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2272 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s3_2272 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w29 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_2273 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2273 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(2,true)),(false,(4,true),(0,true))] s3_2273 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w29 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w38 rfl)))))))))) (by decide +kernel)
theorem b3_2274 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2274 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2274 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w39 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2275 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2275 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2275 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w39 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w25 rfl)))))))))) (by decide +kernel)
theorem b3_2276 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2276 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2276 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w43 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2277 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2277 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2277 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w43 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w52 rfl)))))))))) (by decide +kernel)
theorem b3_2278 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2278 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2278 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2279 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2279 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2279 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w52 rfl)))))))))) (by decide +kernel)
theorem b3_2280 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2280 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(1,true),(3,true))] s3_2280 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w55 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2281 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2281 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(5,true),(1,true))] s3_2281 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w56 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2282 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2282 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(5,true),(3,true))] s3_2282 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2283 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2283 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_2283 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2284 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2284 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_2284 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w52 rfl)))))))))) (by decide +kernel)
theorem b3_2285 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2285 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_2285 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffaaaaffffaaaa] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w58 rfl)))))))))) (by decide +kernel)
theorem b3_2286 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2286 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_2286 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons pc34w52 rfl)))))))))) (by decide +kernel)
theorem b3_2287 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2287 := by
  apply PetersenIndexedNode.close (bank := [s4_1583,a5075,s4_2005,s4_2023,a5076,a5077,a5078,s4_2090,s4_1864,s4_1863,s4_1862,a5079,s4_1850,s4_1849,s4_1848,s4_2024,a5080,a5081,a5034,s4_1907,a5082,a5083,s4_1,a5027,s4_597,a5084,a5085,s4_2091,s4_1957,a5086,a5087,s4_2025,a5088,a5089,a5090,a5091,a5019,a5092,s4_2092,s4_2019,a5093,a5094,s4_2060,a5095,s4_1041,a5096,a5097]) (PetersenIndexedNode.reasons 256 17 417 0xc4442800140012000c28248003111185048444480014000a00092028016a48092001002c48002480a005c92024800400ad20005202801494808a001002828001480a0054520228004009ca000b02015052c8092000a28248002c0814504b02048000a8292000702015051c808a001002528001c082004c702028000a828a0010024800a08406002c2a0a1080a602050409800480032301200098086460240212000282048001602050405800280012100a0005808242014020a00028202800400889080484080108a0805041002314100a0820040484024200a82890802a0251410a08054042a0a14100a829450448402420250100c04940048002120120009404424024011200006024800150100c045400280031300a0005404626014010a000060228004007909008480800e818080c05001f03010180a003884804240400680c0406021505098884c05001b1311018885414060203010b0900c0406021410038281c042c24070501828504006020301248084c48920248004006120009202800ca4809200026244800148084c485202280018980a0005202313014808a000262428004005e002a0301800b0989006022a0a800a8a82a0028262413124004e0024280a1511098905440282080080a0805445001114110a0804c4828200301189800c0484801312098800c042624030121200c4c06260488080c092200900041c124001220283824800a400006049000288080c08a200500030b014000a2026160280094000060450008007400360019000b018100c0a001e030201814002a00130008800300c0806042a0a109008c0a000e212010900a8280604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030280020848042402624018100c0a000a0302018109890424021206222141010808900048402400188889080682024000a0809000614124200840450002820140018504504028201400121005000800114100a081000138301c18200067060383040000a0805040514114100a0802a0a38300a8294504706038300a828a0802a0a242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a0800602313014100a0802624494109890c4c09282313009890a080262430b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1583 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_45 theta)
    · exact b4_2005 theta
    · exact b4_2023 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1645 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2090 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1645 theta)
    · exact b4_2090 theta
    · exact b4_1864 theta
    · exact b4_1863 theta
    · exact b4_1862 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_144 theta)
    · exact b4_1850 theta
    · exact b4_1849 theta
    · exact b4_1848 theta
    · exact b4_2024 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1458 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2091 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1907 theta)
    · exact b4_1907 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_610 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_610 theta)
    · exact b4_1 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_609 theta)
    · exact b4_597 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2092 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1458 theta)
    · exact b4_2091 theta
    · exact b4_1957 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_131 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1800 theta)
    · exact b4_2025 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1957 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_131 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1800 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2025 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_609 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_597 theta)
    · exact b4_2092 theta
    · exact b4_2019 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1041 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_95 theta)
    · exact b4_2060 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2019 theta)
    · exact b4_1041 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_95 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2060 theta)
theorem b3_2288 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2288 := by
  apply PetersenIndexedNode.close (bank := [a5098,s4_1865,a5099,a5100,s4_2093,s4_2020,s4_152,a5101,s4_2069]) (PetersenIndexedNode.reasons 256 17 168 0x480024000a0005000622230a0908890007800340022000ae0606222381818888c282644430a0991102a0a514128a0854142a0a62223818054142a0a6141400105414210110808a0809080484014100a081908048c014100a080908048401410121005040282024200a80854042a0a242001809090084800301018098880c444030101809890084c00301212000c0406024240018084c0406220301018081c04060a030109890c4c0626013120989188890003131209890c4c06260131200c0406022a0a13120a0285440282014110a0800c0426200301189800604616030b000c080604c444622280c080604616030b000c0a0004030201814000406042302109000c0806040b02018500c0806040602109200c084240030201810848200005040282024201a0805040484014100a080908028201c180e0c0504028200a828e0c02a0a24200a08090802820282001808a8800602282009890c4c02624282000c08a2800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_2358 theta)
    · exact b4_1865 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1849 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2093 theta)
    · exact b4_2093 theta
    · exact b4_2020 theta
    · exact b4_152 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_153 theta)
    · exact b4_2069 theta
theorem b3_2289 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2289 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2289 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w62 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2290 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2290 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2290 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w62 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w72 rfl)))))))))) (by decide +kernel)
theorem b3_2291 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2291 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2291 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0x0,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w68 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w62 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w72 rfl))))))))) (by decide +kernel)
theorem b3_2292 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2292 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2292 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w73 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2293 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2293 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s3_2293 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w49 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w73 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w52 rfl)))))))))) (by decide +kernel)
theorem b3_2294 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2294 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2294 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2295 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2295 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2295 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl)))))))))) (by decide +kernel)
theorem b3_2296 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2296 := by
  apply PetersenIndexedNode.close (bank := [s4_1442,a5102,s4_1763,a5103,s4_2008,s4_2049,a5104,a5105,s4_1869,a5106,a5107,s4_2050,a5108,a5109,s4_1913,s4_1912,a5110,a5111,s4_1,a5047,a5112,a5113,s4_1962,a5114,a5115,s4_2052,a5116,a5117,a5118,s4_2054,a5119,a5120,a5121,s4_2060,a5122,a5123,s4_1139,a5124,s4_2065]) (PetersenIndexedNode.reasons 256 17 417 0x92028012a48092001002448002480a004c920248004008d2000c4442901148092000c2824800311118504c444480014809200100228008140020024520228002c0804202b0004800282012000b0205040240812000210148004008042022101800f8a8285415002115050a82a003c210110809c88842022101290118504a404722230a094888a40421011080a602050409800480032301200098086460240212000282048004007050402820800d8a8885445001d15110a88a0034282014101682850405a02290112100a4045a0a242014828a404282029010a0209080280010808a0805000280814100a020420248401080a50100c049400480021201200094044240240112000060248004006109008480800b818080c05001903010180a002c84804240400500c040602290131300a4050015626031300a40406020301094140c042501108089888420225051311084144202060210808b0900c0406021410038281c042c240705018285040060203012480884809202480030b01200092026160248092000424048004004e002203018009109000602520280089480a0020424021204003e001c50021505109005414210131300840454146260150508404848021011511109005444282080060a0805445000d15110a080848028200301109000c0484802322119000c04464403012120084804240488080c092200900041c124001220283824800a40000604900080050848042410009018100c0a0016030201814002042402120800300c080604520230b01480a000e616030b01480806040302108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c0886820302018110900424021206222141010808900048402400188889080682024000a080900080022420121010003282014102000a50402820400092100908061412420084045202282010809850450402820148092100520230a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060221201410084810001494124a0884809282212040000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1442 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_372 theta)
    · exact b4_1763 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_161 theta)
    · exact b4_2008 theta
    · exact b4_2049 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1479 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2076 theta)
    · exact b4_1869 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_174 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1769 theta)
    · exact b4_2050 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1457 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2094 theta)
    · exact b4_1913 theta
    · exact b4_1912 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_938 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_946 theta)
    · exact b4_1 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_945 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1467 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2085 theta)
    · exact b4_1962 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_178 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1767 theta)
    · exact b4_2052 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1971 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_176 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1765 theta)
    · exact b4_2054 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1921 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_194 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1144 theta)
    · exact b4_2060 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_937 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2032 theta)
    · exact b4_1139 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_196 theta)
    · exact b4_2065 theta
theorem b3_2297 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2297 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_2297 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w84 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w78 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w75 rfl)))))))))) (by decide +kernel)
theorem b3_2298 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2298 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2298 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2299 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2299 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2299 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w25 rfl)))))))))) (by decide +kernel)
theorem b3_2300 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2300 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s3_2300 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w89 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_2301 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2301 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s3_2301 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w34 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w89 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w38 rfl)))))))))) (by decide +kernel)
theorem b3_2302 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2302 := by
  apply PetersenIndexedNode.close (bank := [a5125,a5126,s4_2007,a5127,s4_1794,a5128,s4_2009,s4_2058,a5129,a5130,s4_1870,a5131,a5132,s4_2059,a5133,s4_2092,s4_1916,a5134,a5135,s4_2060,s4_1963,a5136,a5137,s4_2061,a5138,s4_2095,a5139,a5140,a5141,a5142,a5143,a5144,s4_1841,s4_1840,s4_1839,s4_2062,a5145,a5146,a5147,a5148,s4_1,a5149,a5150,a5151,a5152,a5153,a5154,a5155,a5156]) (PetersenIndexedNode.reasons 256 17 417 0xb0208017ac0812001002e48002c0820060b0204800400b52000c44438101c0812001002b4800311120058c44448001c0812001002a8013140020050702028002c080c282b0204800383012000b02070602c081200061414800400a6004e21018014185044202702080139c082004c614130a0c0096004850204c040a081300090006460240013010c8c0480424000504090008011400860041001f14100a0820046282014104007a003b001c800d0a0805040702024201c0820036484024201c08050402820800c121009080614114100a08200322820141018504908048404a020180928009000424024001280884804802240000c049000800b018080c05001513110988a002e26221311400500c0406023a12018080c04702062601c080e848c4c038121c0800c04060232a2818080c046141131109888ca8a26221311185040c0406021612018080c04282007050380858480e0a03050a0800c040602490100c052400900041c0a40012404838148012400006029000800900c04060300111312098920026262413124004006020301391100c040602702021201c080e444424038111c08006020301800700c0406026141131209892001e262413121850406020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301488080c092200900041c124001220283824800a400006049000800600c080605000b109008482001a212010904002806040302800400c080604702030b01c0820012616030b01c0800604030230a080c080604e0c0109008480c28221201090383000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c0006020302018081810424006046222141010808900048402400188889080682024000a080900080032420121010005282014102000e504028204001121009080800124200c444702028201c0820006504028201c0812100702030a094100a0810001383014180c2827060382040000a0805040242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060221201410084800301494100c0484809282212000c04a080030130b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b4_1443 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_373 theta)
    · exact b4_2007 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2074 theta)
    · exact b4_1794 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_36 theta)
    · exact b4_2009 theta
    · exact b4_2058 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1480 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2075 theta)
    · exact b4_1870 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_129 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1801 theta)
    · exact b4_2059 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_614 theta)
    · exact b4_2092 theta
    · exact b4_1916 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_80 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1042 theta)
    · exact b4_2060 theta
    · exact b4_1963 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_51 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1585 theta)
    · exact b4_2061 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1637 theta)
    · exact b4_2095 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1630 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2081 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1968 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1969 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1967 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_142 theta)
    · exact b4_1841 theta
    · exact b4_1840 theta
    · exact b4_1839 theta
    · exact b4_2062 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1919 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1918 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_595 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_675 theta)
    · exact b4_1 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_674 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_594 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_637 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2082 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2029 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1052 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_84 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2065 theta)
theorem b3_2303 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2303 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_2303 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w84 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons pc39w90 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w75 rfl)))))))))) (by decide +kernel)
theorem b3_2304 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2304 := by
  apply PetersenIndexedNode.close (bank := [s4_1385,a5157,s4_1859,s4_1880,s4_1438,a4891,s4_1902,s4_1945,s4_1553,a5158,s4_1952,s4_1991,a5159,a5160,a5161,a5162,a5163,a5164,a5165,a5166,s4_1621,a5167,s4_2006,s4_2041,a5168,s4_261,a5169,a5170,s4_1854,a5171,a5172,s4_1949,s4_1858,a5173,a5174,s4_1994,a5175,a5176,a5177,a5178,a5179,a5180,a5181,a5182,s4_1866,a5183,a5184,s4_2044,a5185,s4_459,a5186,a5187,s4_1884,a5188,a5189,s4_1998,s4_1893,a5190,a5191,s4_2002,s4_1906,a5019,a5027,s4_2022,s4_1911,a5122,a5047,s4_2048,s4_1917,s4_594,a5048,a4172,s4_1951,a5192,a5193,s4_2004,a5194,a5195,a5196,a5197,s4_1959,a5198,a5199,s4_2051,s4_1964,s4_871,a5200,a5201,a5202,a5203,a5204,a5205,a5206,a5207,a5208,s4_2053,a5209,a5210,a5211,a5212,a5213,a5150,a5149,s4_2057,a4391,s4_937,a5214,a4394,s4_2026,a5215,a5216,s4_2064]) (PetersenIndexedNode.reasons 256 17 448 0x803731110a00050008036a4001850490008037b111185048444803624000a000500080352c0804202b0008034a4001410090008035ac081410090208034240004202900080331c08042027000803294000c282500080339c080c282502080321400042025000803126020504098008030a4001918090008031a60219180900880302400050409000802f1602050405800802e9400090805000802f9602090805008802e1400050405000802d0a02090802800802c8840450402800802d8a02050402808802c0840490802101802b250100c049400802aa400109009000802ba501109009004802a240000c0490008029150100c04540080289400189805000802995011898050048028140000c0450008027094140c0425018026884044c4421018027894144c4421058026084040c04210180250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c040602802324808060292008022a4001070290008023a4809070290028022240000602900080211480806025200802094000848050008021948088480500280201400006025000801f0a82806020301801e884044c482101801f8a8284c48280a801e0840406020301801d0a88806020301801c8a08016120b01801d8a88816120309801c0a08006020301801b0180806020600801aa12000c080600801b818080c080602801a2120006020301801924404060491008018a4001070490008019a4405070490018018240000604900080171440406045100801694000c2c05000801794404c2c05001801614000060450008015084040604210080148a020424021008015884044240210180140a020060403028013125040604030280128a08016140b028013925041614030a80120a08006040302801121604060403028010818084a4806028011a16044a48212480100180806040302800f00c0442400300800e8181006040300800f80c0406040301800e0181042400604800d31110a0808404800ca400121009000800db11112100d040800c24000a0809000800b30a0921004202800a94000a0805000800bb0a08a0805040800a1400121005000800918504a0805040800888404e0c02101800998504e0c07040800808404a0802101800712100a080484080068a081311028208007921013110484080060a080a0802820800521200a0805040800481808a88806028005a1200a8885440800401808a0800602800310900a0804240800280c052504030180039090125044240800200c04a0800301800118580a0805040800080c08a2820302800198580a2825140800000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1385 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1378 theta)
    · exact b4_1859 theta
    · exact b4_1880 theta
    · exact b4_1438 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_370 theta)
    · exact b4_1902 theta
    · exact b4_1945 theta
    · exact b4_1553 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1370 theta)
    · exact b4_1952 theta
    · exact b4_1991 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1553 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1370 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1952 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1991 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1438 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_370 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1902 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1945 theta)
    · exact b4_1621 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_261 theta)
    · exact b4_2006 theta
    · exact b4_2041 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1621 theta)
    · exact b4_261 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2006 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2041 theta)
    · exact b4_1854 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_876 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1644 theta)
    · exact b4_1949 theta
    · exact b4_1858 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1558 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1563 theta)
    · exact b4_1994 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1858 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1558 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1563 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1994 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1854 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_876 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1644 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1949 theta)
    · exact b4_1866 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_459 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1478 theta)
    · exact b4_2044 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1866 theta)
    · exact b4_459 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1478 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2044 theta)
    · exact b4_1884 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1636 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_881 theta)
    · exact b4_1998 theta
    · exact b4_1893 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1456 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_464 theta)
    · exact b4_2002 theta
    · exact b4_1906 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_609 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_609 theta)
    · exact b4_2022 theta
    · exact b4_1911 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_937 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_945 theta)
    · exact b4_2048 theta
    · exact b4_1917 theta
    · exact b4_594 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_674 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2057 theta)
    · exact b4_1951 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1389 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1389 theta)
    · exact b4_2004 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1893 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_464 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1456 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2002 theta)
    · exact b4_1959 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_469 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1466 theta)
    · exact b4_2051 theta
    · exact b4_1964 theta
    · exact b4_871 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1629 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2053 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1884 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_881 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1636 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1998 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1964 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_871 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1629 theta)
    · exact b4_2053 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1959 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_469 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1466 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2051 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1917 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_594 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_674 theta)
    · exact b4_2057 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1911 theta)
    · exact b4_937 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_945 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2048 theta)
    · exact b4_2026 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_636 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_636 theta)
    · exact b4_2064 theta
theorem b3_2305 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2305 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2305 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 rfl))))))))) (by decide +kernel)
theorem b3_2306 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2306 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2306 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons pc26w91 rfl)))))))))) (by decide +kernel)
theorem b3_2307 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2307 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_2307 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w84 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w75 (PetersenWireProjection.cons pc39w92 rfl)))))))))) (by decide +kernel)
theorem b3_2308 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2308 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2308 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w25 (PetersenWireProjection.cons pc30w93 rfl)))))))))) (by decide +kernel)
theorem b3_2309 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2309 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true))] s3_2309 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x32323232323232323232323232323232,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w91 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
