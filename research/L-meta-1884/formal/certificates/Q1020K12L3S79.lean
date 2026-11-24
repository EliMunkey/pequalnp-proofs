import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S35
import Q1020K12L4S41
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S50
import Q1020K12L4S51
import Q1020K12L4S52
import Q1020K12L4S53
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S59
import Q1020K12L4S63
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S69
import Q1020K12L4S70
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc30w1 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl

private theorem pc30w0 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffaaffaaffffffffffaaffaa := PetersenWireProjection.derive 3 pc30w1 stored8 rfl rfl


private theorem pc30w7 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w6 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w7 stored10 rfl rfl






private theorem pc34w15 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl


private theorem pc34w17 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w14 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffccccffffccccffffffffffffccccffffccccffffcccc : BitVec 256) = 0xfafaaaaafafaaaaafafaaaaafafaaaaa := PetersenWireProjection.derive 3 pc34w15 pc34w17 rfl rfl



private theorem pc34w23 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w24 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc34w17 stored18 rfl rfl
private theorem pc34w26 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w25 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc34w26 stored17 rfl rfl


private theorem pc0w27 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl

private theorem pc0w31 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffccffcc := PetersenWireProjection.derive 3 stored49 stored55 rfl rfl
private theorem pc0w33 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w30 : PetersenPackedPin.project cycle0 (0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w31 pc0w33 rfl rfl








private theorem pc73w40 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl

private theorem pc73w44 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored129 stored131 rfl rfl
private theorem pc73w43 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w44 pc73w40 rfl rfl






private theorem pc29w52 : PetersenPackedPin.project extra29 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored153 stored156 rfl rfl


private theorem pc29w54 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl
private theorem pc29w51 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w52 pc29w54 rfl rfl







private theorem pc26w63 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl

private theorem pc26w62 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w63 stored1 rfl rfl
private theorem pc26w67 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl




private theorem pc29w73 : PetersenPackedPin.project extra29 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored153 stored156 rfl rfl
private theorem pc29w72 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w73 pc29w54 rfl rfl
private theorem pc29w75 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w74 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w75 stored155 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w76 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w77 pc26w78 rfl rfl
private theorem pc30w80 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffcfcfcfcfffffffffffffffffffffffffcfcfcfc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc30w80 pc30w81 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w83 stored0 rfl rfl
private theorem pc29w84 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w75 stored153 rfl rfl
private theorem pc29w86 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc29w87 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored155 stored156 rfl rfl
private theorem pc29w85 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w86 pc29w87 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc0w92 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w91 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w92 stored49 rfl rfl
private theorem pc30w93 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc30w94 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl


private theorem pc74w95 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl

private theorem pc74w98 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored113 stored119 rfl rfl
private theorem pc74w100 : PetersenPackedPin.project extra74 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored119 rfl rfl





private theorem pc26w106 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w78 stored1 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w67 stored0 rfl rfl
private theorem pc30w108 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc30w1 stored9 rfl rfl
private theorem pc29w109 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w54 stored153 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0 := PetersenWireProjection.derive 3 pc26w111 stored0 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xf000f000f000f000f000f000f000f00 := PetersenWireProjection.derive 2 stored9 stored14 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffff0000000000000000cccccccccccccccc : BitVec 256) = 0xffffffff0f000f00ffffffff0f000f00 := PetersenWireProjection.derive 3 pc30w113 stored8 rfl rfl
theorem b3_3318 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3318 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,false),(6,true))] s3_3318 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffaaffaaffffffffffaaffaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w0 rfl)))))))))) (by decide +kernel)
theorem b3_3319 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3319 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,false)),(false,(0,true),(1,true))] s3_3319 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaafafaaaaafafaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w14 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3320 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3320 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(1,true),(5,true))] s3_3320 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w24 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w23 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3321 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3321 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(0,false),(5,true))] s3_3321 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xfffffafafffffafafffffafafffffafa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w24 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w25 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3322 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3322 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(0,true),(3,true))] s3_3322 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w24 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3323 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3323 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3323 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w30 (PetersenWireProjection.cons pc0w27 rfl))))))))) (by decide +kernel)
theorem b3_3324 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3324 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_3324 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons pc73w43 (PetersenWireProjection.cons pc73w40 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_3325 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3325 := by
  apply PetersenIndexedNode.close (bank := [s4_2423,s4_1216,a5899,s4_2913,s4_2771,s4_204,a5768,s4_2910,a5900,a5901,a5902,a5903,a5904,a5905,a5906,a5907,a5908,a5909,s4_1762,a5910,a5911,a4764,a4854,a5912,a4108,a4107,a5913,a5914,a4704,s4_902,a5915,a5916]) (PetersenIndexedNode.reasons 256 17 432 0x51114007924248404800ea10114445001f5111210120038840470301080884048404614121011c0c0c28242222101084044202800d108088405001931111888a0036622231114006084044202501008405400084045040280014040a08050102101042022101800b084044203001551410a82a002ea2825141400504202210131110840442024202706010808c444e0c0311110808420221014808141012000840448402400120209080480821010a0808404800914100a081001138301c18200267060383040040a0805040280824200a0004202282014000a0205040280810809210042021888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840480070a0805041000d15110a88a001e2a221511400305040282024040a0809000420224201200090104840240410808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406028005018080c05000913110988a001626221311400200c0406022606018080c0442026260108089818c4c02406108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602511100c04060284046160210114444c2c048092101006020301800300c0406030005313009892000e626031304001006020301210100c04840048082120108008404424021011202006020301514100c04060221013130084054504626014050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c1210110a0a83824202a101006040302800100c0806050001119108c8a0006232211914000006040302248480c080604420230b0108089212616024049080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2423 theta
    · exact b4_1216 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1762 theta)
    · exact b4_2913 theta
    · exact b4_2771 theta
    · exact b4_204 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_902 theta)
    · exact b4_2910 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2423 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1216 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1762 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2913 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2423 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1216 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1762 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2913 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2423 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1216 theta)
    · exact b4_1762 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2913 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2771 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_204 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_902 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2910 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2771 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_204 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_902 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2910 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2771 theta)
    · exact b4_902 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_204 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2910 theta)
theorem b3_3326 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3326 := by
  apply PetersenIndexedNode.close (bank := [s4_2781,a5917,s4_2909,s4_204,a5726,a4628]) (PetersenIndexedNode.reasons 256 17 173 0x8404420240012000700058001288894040a222501010808c44462222101108094040e060210112020840442022404084044202a0205040210914100a282514128200c4444202311110808a08070603830141016040a020501828080a0807060383014100a0005000280810808a0807060383014100908028201410121005040a02064600a08050402a2215110a08090004800240410808908028201410121005040382014180a0800c0426221311018080c04a020501201809090006020301212000c0442022406018080c0426221311018080c0416020309018080c040e0203050180a000262603130400014444a0205111280800602030121011202084044808514118980c4c0a0803130141012504504015110a080544428200301199800c0462600181084804240030201812808107040302109000c08060421200181108089012030201810848042400302018104c0806240302018102c080614030201810180842480302109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2781 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1158 theta)
    · exact b4_2909 theta
    · exact b4_204 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_222 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2918 theta)
theorem b3_3327 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3327 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3327 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons pc29w51 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3328 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3328 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(1,true))] s3_3328 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3329 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3329 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3329 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons pc29w72 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3330 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3330 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3330 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons pc29w74 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3331 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3331 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(7,true),(0,false))] s3_3331 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3332 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3332 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(1,true),(0,false))] s3_3332 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3333 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3333 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3333 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w33 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3334 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3334 := by
  apply PetersenIndexedNode.close (bank := [s4_2909,s4_222,a5726,s4_2926]) (PetersenIndexedNode.reasons 256 17 170 0x108088404800140006000700005111280814444a020210118888c4444202210128081c0c04202240410808420221015010282010848a080514128a09410062222101188888404504038301c180a080b0205010280c140409080282014101210052022101108488404504038301c180a080484014100a080908028205010323005040282015110a88850404a022101108288404484014100a080908028201c100a0c0504006021311098880c0406025010280900c048480030101809090006022101313000c0406021311098880c0406020b01018480c0406020701018280c0442403130189808480a222501028889404003010180908088480480a212018980c4c042402120141012504424015110a080544428200301119000c0442400181084804240030201812808107040302109000c0806042120018110808c2c0030201810848042400302018104c0806240302018102c080614030201810180842480302109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact b4_2909 theta
    · exact b4_222 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_222 theta)
    · exact b4_2926 theta
theorem b3_3335 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3335 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,true),(1,true))] s3_3335 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w82 rfl)))))))))) (by decide +kernel)
theorem b3_3336 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3336 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3336 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w84 rfl)))))))))) (by decide +kernel)
theorem b3_3337 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3337 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3337 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w85 rfl)))))))))) (by decide +kernel)
theorem b3_3338 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3338 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(5,true),(1,true))] s3_3338 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w88 rfl)))))))))) (by decide +kernel)
theorem b3_3339 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3339 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,true),(1,true))] s3_3339 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w90 rfl)))))))))) (by decide +kernel)
theorem b3_3340 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3340 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3340 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w33 (PetersenWireProjection.cons pc0w91 rfl))))))))) (by decide +kernel)
theorem b3_3341 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3341 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(4,true),(3,true))] s3_3341 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons pc30w94 (PetersenWireProjection.cons pc30w93 rfl)))))))))) (by decide +kernel)
theorem b3_3342 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3342 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_3342 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w100 (PetersenWireProjection.cons pc74w98 (PetersenWireProjection.cons pc74w95 rfl)))))))))) (by decide +kernel)
theorem b3_3343 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3343 := by
  apply PetersenIndexedNode.close (bank := [a5918,a5919,s4_2440,s4_2439,s4_2438,a5920,a5921,a5922,a5923,s4_2914,a5924,a5925,s4_3,a5926,a5927,a5928,a5929,a5930,a5931,a5932,a5933,a5934,a5935,a5936,a5937,a5938,a5939,a5940,a5941,s4_1785,a5942,a5943,a5944,a4847,s4_2918,a5945,a4759,a4704,s4_1179,a5915,s4_2926]) (PetersenIndexedNode.reasons 256 17 420 0x49094009d2424840480132101124250028490921012004a8404622210808840484046141308098888c2826222210108404420280124008c9011000c21011080944442a0a5000210114100a000511128201444484041505210120042a0801080c00805414210180110a8285415001f504028200c4442a0a310110808c282420231111850484444202150510809202050404800210112100900048082420120208404282021012003a9080484040070a0805040800f14100a081001b484024200a4249080290110808a080420229091410084244202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a82918182820460221011918084044606323010818840414102101200330018800bc005850402820800d0a08050410015800a4004c9414282025011080890804202250512100841442021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a002284804240400400c0406028009018080c05000f424021200e8680602030110809898042023a1a31300e0684202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092424262449092101185808404490930b0124248404131221012001d000d0180c00304c480301210109890840470302120188808404424021011c0c04c48480a15051090054146141131209890541426241405185048480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080050a0805445000b14110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c120c090a0a83824202a10100604030280044001e000d0005018100c0a0012030201814001200070002800000c080604420230b01080a0002616010b0108080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1492 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2950 theta)
    · exact b4_2440 theta
    · exact b4_2439 theta
    · exact b4_2438 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_172 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1788 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1787 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1786 theta)
    · exact b4_2914 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1492 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2950 theta)
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1008 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1005 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2441 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_171 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1785 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2915 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2440 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2439 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2438 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_172 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1788 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1787 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1786 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2914 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2441 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_171 theta)
    · exact b4_1785 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2915 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2783 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_192 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1155 theta)
    · exact b4_2918 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1008 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1005 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2771 theta)
    · exact b4_1179 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_204 theta)
    · exact b4_2926 theta
theorem b3_3344 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3344 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(7,true),(0,false))] s3_3344 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons pc26w106 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3345 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3345 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(1,true))] s3_3345 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3346 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3346 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,false))] s3_3346 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffafafffffafafffffafafffffafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w107 rfl)))))))))) (by decide +kernel)
theorem b3_3347 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3347 := by
  apply PetersenIndexedNode.close (bank := [s4_2461,s4_2460,s4_2459,a5946,a5947,a5948,a5949,s4_2919,a5950,a5951,s4_3,a5952,a5953,a5954,a5955,a5956,a5957,a5958,a5959,a5960,a5961,a5962,a5963,a5964,a5965,s4_1821,a5966,a5967,a5968,a5969,a4093,a4795,s4_2918,a5970,s4_1091,a5971,a4628]) (PetersenIndexedNode.reasons 256 17 420 0x49094008d24248404801121011242500244909210120042840470301080884048404614130809c0c0c28242222101084044202800f920209011001e21011080a004042022101400749010480850100a829440484045141288094040a28250102101054148404800e4006c4203000a150508404c4442a0a310110809c18042023111383008444420215051080920205040480021011210090004808242012020840428202101200325040282040060e0c07060800d1c180e0c10017282014100a0209080280010808a0805000280814100a0204202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a829181828204602210119180840446063230108188404141021012002a484024204005050402820800b0a0805041001324201210090102820240010808908048002404121009010420214101080854144840150128a0850402a0215050a0805414a28224201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a002284804240400400c0406028009018080c05000f42402120098180602030110809898042022606313009018420203010180a001a060203010a8284c4426028007098880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092424262449092101185808404490930b01242484041312210120019000b0180c00284c48030121010989084044808313012020840462602101120204c484808150530b005414e0c0131209890541426241405383018580280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080040a0805445000914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260428280c080604840441c120c090a0a83824202a10100604030280034001600090003018100c0a000e030201814000a00030000248480c080604420230b010808921261602404908080604030270e080c0806042a0a109008c09c382212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030261e08848042402624018100c098782030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2461 theta
    · exact b4_2460 theta
    · exact b4_2459 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_43 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2108 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2109 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2107 theta)
    · exact b4_2919 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1495 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2951 theta)
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1016 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1014 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1495 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2951 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2465 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_42 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1825 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2921 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2465 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_42 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1825 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2921 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2480 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_41 theta)
    · exact b4_1821 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2923 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1016 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1014 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2790 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_19 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1091 theta)
    · exact b4_2918 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2790 theta)
    · exact b4_1091 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_19 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2918 theta)
theorem b3_3348 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3348 := by
  apply PetersenIndexedNode.close (bank := [a5972,a5973,s4_2462,a5974,a5975,s4_2920,a5976,a5977,s4_1493,a5978,a5979,s4_2672,a5980,a5981,s4_3,a5982,a5983,a5984,a5985,a5986,a5987,a5988,a5989,a5990,a5991,a5992,a5993,a5994,a5995,s4_1822,a5996,a5997,a4065,a4847,s4_2918,a5998,a5999,a5970,s4_1155,a5971,a4676]) (PetersenIndexedNode.reasons 256 17 420 0x49094009d2424840480132101124250028490921012004a8404622210808840484046141308098888c2826222210108404420280124008c9011000e210110809444421011080a10114504a202511128a0944448404108088406004221011080c008054142a0a80110a8285415001f108088404c4442101108090808c282420231111850484444202108088405202050404800210112100900048082420120208404282021012003a9080484040070a0805040800f14100a081001b484024200a4249080290110808a08042022909141008424420248401080862225040188088404e0c0210118889c180422221012820084051818282046022101191808404460632301081884041410210120032282014104006054442a22800d0a8885445001714100a080941428202501108089080420225051210084144202141010808501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a002a84804240400500c040602800b018080c0500134240212020022060203011080989804202800931301898042020301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092424424049092101185808404490930b01242484042120210120021000f0180c0038848003012101400348405000c2120109008404424021014002e0014480a1505109005414210131300840454146260150508404848021014941109008480504080041410125050009494114100848042401511109005444282080030a0805445000715110a080848028200301109000c0484802322119000c04464403012120084804240428280c080604840441c120c090a0a83824202a10100604030280020848042410003018100c0a000a030201814000842402120800000c080604420230b01080a0002616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c088682030201811090042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1493 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2952 theta)
    · exact b4_2462 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_168 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1822 theta)
    · exact b4_2920 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1493 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2952 theta)
    · exact b4_1493 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2952 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2672 theta)
    · exact b4_2672 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_964 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_964 theta)
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1024 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1022 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1493 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2952 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2462 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_168 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1822 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2920 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2462 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_168 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1822 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2920 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2462 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_168 theta)
    · exact b4_1822 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2920 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2790 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1155 theta)
    · exact b4_2918 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1024 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1022 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2790 theta)
    · exact b4_1155 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_19 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2918 theta)
theorem b3_3349 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3349 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_3349 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w106 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3350 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3350 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(0,false),(3,true))] s3_3350 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3351 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3351 := by
  apply PetersenIndexedNode.close (bank := [a6000,a6001,s4_2471,s4_2470,s4_2466,a6002,a6003,a6004,a6005,s4_2922,a6006,a6007,s4_3,a6008,a6009,a6010,a6011,a6012,s4_2924,a6013,a6014,a6015,a6016,a6017,a6018,a6019,a6020,a6021,a6022,s4_1830,a6023,a6024,a4847,a6025,a4795,a5970,s4_1179,a5971,s4_2926]) (PetersenIndexedNode.reasons 256 17 414 0x12425002549092101200488404490940099242484048011a1011888842022101210118504c202622230a098888840421011080a004500212404400308404420250100a829440484045141288094040a2825010210105414840480104007c4203000c150508404c4442a0a310110808c282420231111850484444202150510809202050404800210112100900048082420120208404282021012003a9080484040070a0805040800f14100a081001b484024200a4249080290110808a080420229091410084244202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a82918182820460221011918084044606323010818840414102101200330018800bc005850402820800d0a08050410015800a4004c9414282025011080890804202250512100841442021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a002284804240400400c0406028009018080c05000f424021200e8680602030110809898042023a1a31300e0684202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092424262449092101185808404490930b0124248404131221012001d000d0180c00304c480301210109890840470302120188808404424021011c0c04c48480a15051090054146141131209890541426241405185048480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080050a0805445000b14110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c120c090a0a83824202a10100604030280044001e000d0005018100c0a0012030201814001200070002800000c080604420230b01080a0002616010b0108080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1496 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2953 theta)
    · exact b4_2471 theta
    · exact b4_2470 theta
    · exact b4_2466 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_24 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2204 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2219 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2174 theta)
    · exact b4_2922 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1496 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2953 theta)
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1095 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1091 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2481 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_16 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1830 theta)
    · exact b4_2924 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2471 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2470 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2466 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_24 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2204 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2219 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2174 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2922 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2481 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_16 theta)
    · exact b4_1830 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2924 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1159 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1155 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1095 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1091 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2790 theta)
    · exact b4_1179 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_19 theta)
    · exact b4_2926 theta
theorem b3_3352 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3352 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3352 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w74 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w84 rfl)))))))))) (by decide +kernel)
theorem b3_3353 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3353 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3353 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w74 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w109 rfl)))))))))) (by decide +kernel)
theorem b3_3354 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3354 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3354 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w74 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w85 rfl)))))))))) (by decide +kernel)
theorem b3_3355 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3355 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_3355 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3356 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3356 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(0,false),(3,true))] s3_3356 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3357 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3357 := by
  apply PetersenIndexedNode.close (bank := [s4_2484,s4_2485,s4_2483,s4_11,a6026,a6027,a6028,s4_2927,s4_3,a6029,a6030,a6031,a6032,a6033,a6034,a6035,a6036,a6037,a6038,a6039,a6040,a6041,a6042,a6043,a6044,a6045,a6046,a6047,a6048,a6049,a6050,s4_2243,s4_2244,s4_2242,a6051,a6052,a6053,a6054,a5765,s4_1183,s4_1179]) (PetersenIndexedNode.reasons 256 17 408 0x80144009d08090008490921012004d002524044002084044202622210808840492126141308098888c2824222248488404420280124008c4203000815050840540402a0a5101248494100a2025010282014040921215050a828c4442a0a310110808c28242023111185048444420215051080a00430020800fc0078a0805040801114100a081001d800e4006d24245040490128081210092024909242012424a020282028080a4249080290110808a080420229091410084244202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a82a00330018800bc005850402820800d0a08050410015800a4004d343428204d0924849918092124d0d32301243492121410248489414282025011080890804202250512100841442021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a082002300108007c00380c0406028009018080c05000d80064002d484806020301248490900860252122120140489212030101808e8680602030110809898042023a1a31300e0684202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a001500090180c00204c4803014909098912424a02041c0a8081242483814809280804c489012210109890840470302120188808404424021011c0c04c48480a15051090054146141131209890541426241405185048480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301109000c0484801312098800c0426240301212008480424080034001600090003018100c0a000e030201814000a0003000062a280c080604921241c120c098a8a83826222a48480604030264c480c080604420230b0108099312616010b0108080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2484 theta
    · exact b4_2485 theta
    · exact b4_2483 theta
    · exact b4_11 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2243 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2244 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2242 theta)
    · exact b4_2927 theta
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1183 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1179 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2484 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2485 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2483 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_11 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2243 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2244 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2242 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2927 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2484 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2485 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2483 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_11 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2243 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2244 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2242 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2927 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2484 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2485 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2483 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_11 theta)
    · exact b4_2243 theta
    · exact b4_2244 theta
    · exact b4_2242 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2927 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1183 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1179 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1183 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1179 theta)
    · exact b4_1183 theta
    · exact b4_1179 theta
theorem b3_3358 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3358 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(3,true))] s3_3358 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf5f5f0f0f5f5f0f0f5f5f0f0f5f5f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons pc26w89 rfl))))))))) (by decide +kernel)
theorem b3_3359 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3359 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true)),(false,(0,true),(6,true))] s3_3359 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff0f000f00ffffffff0f000f00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w112 (PetersenWireProjection.cons pc30w93 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
