import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S25
import Q1020K12L4S28
import Q1020K12L4S35
import Q1020K12L4S38
import Q1020K12L4S43
import Q1020K12L4S48
import Q1020K12L4S50
import Q1020K12L4S56
import Q1020K12L4S58
import Q1020K12L4S59
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S71
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc32w2 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl

private theorem pc32w1 : PetersenPackedPin.project extra32 (0xffffffffffffffffffccffccffccffccffffffffffffffffffccffccffccffcc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc32w2 stored25 rfl rfl

private theorem pc32w6 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl






private theorem pc34w13 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl

private theorem pc34w12 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffccccffffccccffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w13 stored17 rfl rfl

private theorem pc34w17 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl






private theorem pc2w23 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl

private theorem pc2w26 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl







private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl

private theorem pc26w33 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w34 stored1 rfl rfl

private theorem pc26w38 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl





private theorem pc29w45 : PetersenPackedPin.project extra29 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored153 stored155 rfl rfl


private theorem pc29w47 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w44 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w45 pc29w47 rfl rfl




private theorem pc29w54 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w47 stored155 rfl rfl
private theorem pc26w56 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffeeeeeeeeffffffffffffffffffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w56 pc26w38 rfl rfl



private theorem pc30w59 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl

private theorem pc30w58 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc30w59 stored9 rfl rfl

private theorem pc30w63 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl



private theorem pc30w69 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w68 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffcfcfcfcfffffffffffffffffffffffffcfcfcfc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc30w69 pc30w59 rfl rfl
private theorem pc32w71 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w70 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w71 stored25 rfl rfl
private theorem pc32w73 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w72 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffccffccffffffffffffffffffffffffffccffcc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc32w73 pc32w71 rfl rfl
private theorem pc34w75 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc34w74 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w75 stored17 rfl rfl
private theorem pc34w77 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffccccffffffffffffffffffffffffffffcccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc34w77 pc34w75 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w56 stored0 rfl rfl
private theorem pc29w80 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl
private theorem pc29w79 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w80 stored153 rfl rfl
private theorem pc30w82 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w82 stored8 rfl rfl
private theorem pc34w84 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc34w83 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w84 stored16 rfl rfl
private theorem pc29w86 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc29w87 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored155 stored156 rfl rfl
private theorem pc29w85 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w86 pc29w87 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfffffffffffffffffffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w38 stored0 rfl rfl


private theorem pc3w93 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w93 stored33 rfl rfl

private theorem pc3w97 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl




private theorem pc30w103 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc30w104 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl


private theorem pc75w105 : PetersenPackedPin.project extra75 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored209 stored210 rfl rfl

private theorem pc75w108 : PetersenPackedPin.project extra75 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored209 stored211 rfl rfl

private theorem pc75w110 : PetersenPackedPin.project extra75 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored212 stored211 rfl rfl




private theorem pc32w116 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc32w117 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc34w119 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w120 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc26w122 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w121 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w122 pc26w123 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeeffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w125 pc26w34 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w123 stored2 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w38 stored1 rfl rfl
private theorem pc30w130 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w131 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w129 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0 := PetersenWireProjection.derive 3 pc30w130 pc30w131 rfl rfl
private theorem pc30w133 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w132 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffff0f0f0f0fffffffffcfcfcfcfffffffff0f0f0f0 : BitVec 256) = 0xfaaafaaafaaafaaafaaafaaafaaafaaa := PetersenWireProjection.derive 3 pc30w133 pc30w59 rfl rfl
private theorem pc30w135 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff0000000000 := PetersenWireProjection.derive 0 stored8 stored14 rfl rfl
private theorem pc30w134 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa := PetersenWireProjection.derive 3 pc30w135 pc30w59 rfl rfl
private theorem pc30w136 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w131 stored10 rfl rfl
private theorem pc30w137 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc30w63 stored9 rfl rfl
private theorem pc30w138 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl
theorem b3_3276 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3276 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,true),(6,true)),(false,(1,true),(5,true))] s3_3276 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w1 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3277 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3277 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(1,true),(5,true))] s3_3277 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w12 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3278 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3278 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3278 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w26 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w23 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_3279 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3279 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_3279 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3280 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3280 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3280 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w47 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w44 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3281 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3281 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3281 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w47 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3282 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3282 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_3282 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3283 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3283 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(1,true),(3,true))] s3_3283 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w63 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w58 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3284 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3284 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(0,false),(3,true))] s3_3284 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w63 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w68 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3285 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3285 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_3285 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3286 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3286 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,true),(6,true)),(false,(0,false),(5,true))] s3_3286 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w72 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3287 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3287 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_3287 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w74 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3288 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3288 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true)),(false,(0,false),(5,true))] s3_3288 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xfffffafafffffafafffffafafffffafa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w76 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3289 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3289 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3289 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w26 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_3290 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3290 := by
  apply PetersenIndexedNode.close (bank := [s4_2358,a5875,a5876,a5098,s4_2022,a5877,s4_2894,s4_155,a5874,s4_2926]) (PetersenIndexedNode.reasons 256 17 170 0x1080884042101108098888c282422240022000f00098003381818888e060622230a099110c28264440a8294504a28215050a8298888e06015050a829850500051505084044203000428201410200065040682024200a08090802820141012100504038301c180a0803a0a15050a8685414282024201210050402820642012300504028202420121005040484014100a08090802a0215010a828908028201c100a0c0504006024240212000c0406026220311100c0406026240213000c048480030101809090006021301018880c0406020b01018480c0406020701018280c0426243130189804c4826246222400084c4826243130189804c48030101808a8284c48280a13120d8904c68262415100a080504428200301098800c046260018118580c2c00302018131111888a0302018118580c2c00302800080c0806050000018108c0842400302018104c0806240302018102c080614030201810180842480302109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2358 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2022 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3011 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2358 theta)
    · exact b4_2022 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_3011 theta)
    · exact b4_2894 theta
    · exact b4_155 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_155 theta)
    · exact b4_2926 theta
theorem b3_3291 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3291 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(1,true),(3,true))] s3_3291 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w78 rfl)))))))))) (by decide +kernel)
theorem b3_3292 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3292 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3292 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w47 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w79 rfl)))))))))) (by decide +kernel)
theorem b3_3293 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3293 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(1,true),(4,true))] s3_3293 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w63 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w81 rfl)))))))))) (by decide +kernel)
theorem b3_3294 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3294 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(1,true),(3,true))] s3_3294 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w83 rfl)))))))))) (by decide +kernel)
theorem b3_3295 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3295 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3295 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w47 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w85 rfl)))))))))) (by decide +kernel)
theorem b3_3296 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3296 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(5,true),(3,true))] s3_3296 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w88 rfl)))))))))) (by decide +kernel)
theorem b3_3297 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3297 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(7,true),(3,true))] s3_3297 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w90 rfl)))))))))) (by decide +kernel)
theorem b3_3298 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3298 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,false),(3,true))] s3_3298 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffffffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w91 rfl)))))))))) (by decide +kernel)
theorem b3_3299 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3299 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3299 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w97 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w92 rfl))))))))) (by decide +kernel)
theorem b3_3300 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3300 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(5,true)),(false,(4,true),(1,true))] s3_3300 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w63 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w104 (PetersenWireProjection.cons pc30w103 rfl)))))))))) (by decide +kernel)
theorem b3_3301 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3301 := by
  intro m le c
  apply rejects_sound extra75 i6 5 tgt small75 hot75 [] s3_3301 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xffffffffffffffff,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xcccccccccccccccc,0xffffffffffffffff,0x0,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored216 (PetersenWireProjection.cons stored211 (PetersenWireProjection.cons stored215 (PetersenWireProjection.cons stored214 (PetersenWireProjection.cons stored213 (PetersenWireProjection.cons stored212 (PetersenWireProjection.cons pc75w110 (PetersenWireProjection.cons stored210 (PetersenWireProjection.cons pc75w108 (PetersenWireProjection.cons pc75w105 rfl)))))))))) (by decide +kernel)
theorem b3_3302 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3302 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(7,true),(3,true))] s3_3302 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w117 (PetersenWireProjection.cons pc32w116 rfl)))))))))) (by decide +kernel)
theorem b3_3303 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3303 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(7,true),(1,true))] s3_3303 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w117 (PetersenWireProjection.cons pc32w118 rfl)))))))))) (by decide +kernel)
theorem b3_3304 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3304 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(3,true),(1,true))] s3_3304 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w17 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w120 (PetersenWireProjection.cons pc34w119 rfl)))))))))) (by decide +kernel)
theorem b3_3305 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3305 := by
  apply PetersenIndexedNode.close (bank := [s4_2377,s4_2376,s4_2375,a5878,a5879,a5880,a5881,s4_2903,a5882,a5883,s4_3,a5884,a5885,s4_780,a5886,a5887,a5888,a5889,s4_2906,a5890,a5891,a5892,a5893,a5894,a5895,s4_1602,s4_2908,a5896,a4815,a5897,a4795,a5898,s4_2918,a5866,s4_1179,a5867,s4_2926]) (PetersenIndexedNode.reasons 256 17 420 0x70301080884048404614130809c0c0c2825030210108404420249094008d24248404801121011242500244909210120042840421014007c8404c888800f1202084050020210132222003ac88850100a829440484045141288094040a2825010210105414840431110a828c404420230a090808c444614121111080854144202800e4006c4203000a150508405202050404800210112100900048082420120208404282021010a4249080290110808a08042022909141008424420248401080a00329080484040060a0805040800d14100a0810017484024200743450401d050a828e0c02a0a1d0d1c18054342a0a28200a82918182820460221011918084044606323010818840414102101094142820250110808908042022505121008414420214101080a002ac8c064604005050402820800b0a080504100136460323005414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a081080806024200240410900840042022120108089010030101808e8680602030110809898042023a1a31300e068420203010180a002284804240400400c0406028009018080c05000f424021200ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180924242624490921012001a8404490940039242484041312210108404262421011c0c0848062202101109008404703013121202a0019000b0180c00284c48030115051090054146141131209890541426241405185048480280a4941098904c4850401b1a0d89125043634131a141004c4826241511098905440282080040a0805445000914110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c120c090a0a83824202a10100604030264c480c080604420230b0108099312616010b0108080604030280034001600090003018100c0a000e030201814000a0003000030a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2377 theta
    · exact b4_2376 theta
    · exact b4_2375 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_62 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2105 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2106 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2104 theta)
    · exact b4_2903 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1494 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2949 theta)
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_832 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_830 theta)
    · exact b4_780 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2983 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2458 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_59 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1818 theta)
    · exact b4_2906 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2456 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_61 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1819 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2907 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2479 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_48 theta)
    · exact b4_1602 theta
    · exact b4_2908 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_838 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_836 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2750 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1091 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_64 theta)
    · exact b4_2918 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2723 theta)
    · exact b4_1179 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_97 theta)
    · exact b4_2926 theta
theorem b3_3306 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3306 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false)),(false,(0,true),(5,true))] s3_3306 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w121 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3307 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3307 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s3_3307 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3308 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3308 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(5,true),(1,true))] s3_3308 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3309 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3309 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_3309 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w128 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3310 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3310 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_3310 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3311 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3311 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(0,false)),(false,(0,true),(4,true))] s3_3311 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w129 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3312 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3312 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(0,true),(1,true))] s3_3312 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfaaafaaafaaafaaafaaafaaafaaafaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w132 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3313 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3313 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(3,false)),(false,(0,true),(1,true))] s3_3313 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaaaaaaaaaffaaffaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w134 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3314 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3314 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(4,true),(3,true))] s3_3314 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w69 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3315 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3315 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(0,false),(3,true))] s3_3315 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w137 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3316 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3316 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(0,true),(1,true))] s3_3316 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3317 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3317 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(1,true),(6,true))] s3_3317 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w136 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w138 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
