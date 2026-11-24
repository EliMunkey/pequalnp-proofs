import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc26w1 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl





private theorem pc26w9 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 pc26w9 pc26w11 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w15 stored1 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc26w14 pc26w9 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w18 stored1 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc26w17 pc26w9 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored6 stored7 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0x5555555544444444555555554444444455555555444444445555555544444444 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w22 pc26w23 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xaaaaaaaabbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaabbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa := PetersenWireProjection.derive 2 pc26w21 pc26w11 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored0 stored1 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w22 pc26w15 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc26w11 pc26w22 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaffffffffaaaaaaaaeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc26w14 pc26w22 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc26w34 pc26w22 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w15 stored0 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc26w36 pc26w22 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w11 stored0 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc26w38 pc26w22 rfl rfl





private theorem pc17w44 : PetersenPackedPin.project tree17 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored169 stored173 rfl rfl
private theorem pc17w46 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored170 stored173 rfl rfl
private theorem pc17w43 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc17w44 pc17w46 rfl rfl


private theorem pc17w51 : PetersenPackedPin.project tree17 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored170 stored175 rfl rfl
private theorem pc17w50 : PetersenPackedPin.project tree17 (0xcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc17w51 stored169 rfl rfl
private theorem pc17w52 : PetersenPackedPin.project tree17 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored173 stored175 rfl rfl
private theorem pc17w49 : PetersenPackedPin.project tree17 (0xcc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc17w50 pc17w52 rfl rfl






private theorem pc32w59 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored26 stored29 rfl rfl

private theorem pc32w58 : PetersenPackedPin.project extra32 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w59 stored28 rfl rfl

private theorem pc32w64 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl
private theorem pc32w63 : PetersenPackedPin.project extra32 (0xcc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w59 pc32w64 rfl rfl








private theorem pc0w73 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w75 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xcc00cc00 := PetersenWireProjection.derive 0 stored49 stored55 rfl rfl
private theorem pc0w76 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl
private theorem pc0w74 : PetersenPackedPin.project cycle0 (0xcccccccc00000000000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w75 pc0w76 rfl rfl

private theorem pc0w78 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w79 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w73 stored50 rfl rfl
private theorem pc0w80 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w81 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored49 stored55 rfl rfl
private theorem pc0w82 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl







private theorem pc2w90 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl
private theorem pc2w92 : PetersenPackedPin.project cycle2 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 stored41 stored42 rfl rfl
private theorem pc2w91 : PetersenPackedPin.project cycle2 (0xcccccccc000000000000000000000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc2w92 pc2w90 rfl rfl

private theorem pc0w95 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xff00 := PetersenWireProjection.derive 1 stored49 stored51 rfl rfl
private theorem pc0w94 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc0w95 pc0w78 rfl rfl
private theorem pc2w97 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored41 stored42 rfl rfl
private theorem pc2w96 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc2w97 pc2w90 rfl rfl
private theorem pc2w99 : PetersenPackedPin.project cycle2 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 stored41 stored42 rfl rfl
private theorem pc2w98 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 3 pc2w99 pc2w90 rfl rfl







private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w108 pc3w109 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

theorem b3_2730 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2730 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(1,true),(7,true))] s3_2730 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2731 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2731 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_2731 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2732 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2732 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_2732 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2733 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2733 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_2733 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2734 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2734 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_2734 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2735 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2735 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,false))] s3_2735 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2736 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2736 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,false),(1,false))] s3_2736 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w24 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2737 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2737 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(1,true),(7,true))] s3_2737 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2738 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2738 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,true),(7,true))] s3_2738 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w26 rfl)))))))))) (by decide +kernel)
theorem b3_2739 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2739 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,true),(1,true))] s3_2739 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w25 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w27 rfl)))))))))) (by decide +kernel)
theorem b3_2740 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2740 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,false),(5,false))] s3_2740 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xf0f00000f0f00000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons pc26w28 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2741 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2741 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(5,true),(7,true))] s3_2741 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2742 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2742 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,true),(5,true))] s3_2742 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w30 rfl)))))))))) (by decide +kernel)
theorem b3_2743 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2743 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,true),(7,true))] s3_2743 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w26 rfl)))))))))) (by decide +kernel)
theorem b3_2744 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2744 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_2744 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffaaaaffffaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2745 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2745 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_2745 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffaaaaffffaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2746 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2746 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,false),(1,false))] s3_2746 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons pc26w32 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2747 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2747 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,true),(7,true))] s3_2747 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w19 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2748 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2748 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,true),(1,true))] s3_2748 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w12 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2749 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2749 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(1,true),(7,true))] s3_2749 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2750 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2750 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,true),(7,true))] s3_2750 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0fffff0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w35 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2751 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2751 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,true),(7,true))] s3_2751 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0fffff0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w35 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w30 rfl)))))))))) (by decide +kernel)
theorem b3_2752 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2752 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_2752 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2753 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2753 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(0,true)),(false,(0,true),(7,true))] s3_2753 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w27 rfl)))))))))) (by decide +kernel)
theorem b3_2754 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2754 := by
  intro m le c
  apply rejects_sound tree17 i6 6 tgt small17 hot17 [] s3_2754 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc,0xffffffff00000000,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons stored176 (PetersenWireProjection.cons pc17w49 (PetersenWireProjection.cons stored175 (PetersenWireProjection.cons stored174 (PetersenWireProjection.cons pc17w43 (PetersenWireProjection.cons stored172 (PetersenWireProjection.cons stored171 (PetersenWireProjection.cons stored170 (PetersenWireProjection.cons stored169 rfl))))))))) (by decide +kernel)
theorem b3_2755 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2755 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(6,true))] s3_2755 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w63 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w58 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_2756 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2756 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(4,false))] s3_2756 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccc0000,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w74 (PetersenWireProjection.cons pc0w73 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2757 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2757 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2757 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w74 (PetersenWireProjection.cons pc0w78 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2758 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2758 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2758 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w74 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2759 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2759 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,false))] s3_2759 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcc00cc00,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w79 (PetersenWireProjection.cons pc0w75 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2760 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2760 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s3_2760 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xff000000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w79 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w80 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2761 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2761 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,true),(3,true))] s3_2761 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffccffcc] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w79 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w81 rfl)))))))))) (by decide +kernel)
theorem b3_2762 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2762 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,true),(3,true))] s3_2762 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w79 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w82 rfl)))))))))) (by decide +kernel)
theorem b3_2763 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2763 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2763 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w91 (PetersenWireProjection.cons pc2w90 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2764 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2764 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2764 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w91 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2765 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2765 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2765 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w94 (PetersenWireProjection.cons pc0w78 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2766 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2766 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2766 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w94 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2767 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2767 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2767 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w96 (PetersenWireProjection.cons pc2w90 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2768 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2768 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_2768 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w96 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_2769 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2769 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,true),(2,true))] s3_2769 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w96 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w97 rfl)))))))))) (by decide +kernel)
theorem b3_2770 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2770 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(4,false),(2,true))] s3_2770 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f0000,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w90 (PetersenWireProjection.cons pc2w98 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_2771 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2771 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2771 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons pc3w107 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
