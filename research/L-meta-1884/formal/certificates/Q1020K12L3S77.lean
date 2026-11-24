import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S5
import Q1020K12L4S9
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S18
import Q1020K12L4S23
import Q1020K12L4S26
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S31
import Q1020K12L4S37
import Q1020K12L4S41
import Q1020K12L4S42
import Q1020K12L4S48
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S71
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0




private theorem pc30w2 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl



private theorem pc30w6 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl

private theorem pc30w11 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xfaf0faf0faf0faf0faf0faf0faf0faf0 := PetersenWireProjection.derive 3 pc30w11 stored9 rfl rfl
private theorem pc30w12 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w13 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored9 stored10 rfl rfl
private theorem pc30w14 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc30w2 stored9 rfl rfl
private theorem pc30w16 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w15 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfffffffff000f000fffffffff000f000 := PetersenWireProjection.derive 3 pc30w16 stored8 rfl rfl
private theorem pc30w17 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc30w18 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl
private theorem pc30w20 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w19 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w20 stored11 rfl rfl
private theorem pc30w21 : PetersenPackedPin.project extra30 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w11 stored11 rfl rfl
private theorem pc30w22 : PetersenPackedPin.project extra30 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff000f000f000f000 := PetersenWireProjection.derive 3 pc30w16 stored11 rfl rfl




private theorem pc2w25 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w29 : PetersenPackedPin.project cycle2 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaa := PetersenWireProjection.derive 3 stored42 stored47 rfl rfl
private theorem pc2w28 : PetersenPackedPin.project cycle2 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 0 pc2w29 pc2w25 rfl rfl







private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl


private theorem pc26w39 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w37 pc26w39 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 0 pc26w43 pc26w44 rfl rfl



private theorem pc30w49 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w50 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w48 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0 := PetersenWireProjection.derive 3 pc30w49 pc30w50 rfl rfl
private theorem pc30w51 : PetersenPackedPin.project extra30 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0 := PetersenWireProjection.derive 0 pc30w12 pc30w2 rfl rfl



private theorem pc32w55 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored25 stored26 rfl rfl


private theorem pc32w57 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl
private theorem pc32w54 : PetersenPackedPin.project extra32 (0xffffffffffccffccffccffccffccffccffffffffffccffccffccffccffccffcc : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w55 pc32w57 rfl rfl
private theorem pc32w61 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w62 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc32w60 : PetersenPackedPin.project extra32 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 0 pc32w61 pc32w62 rfl rfl






private theorem pc34w69 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl


private theorem pc34w71 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w68 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffccccffffccccffffffffffffccccffffccccffffcccc : BitVec 256) = 0xfafaaaaafafaaaaafafaaaaafafaaaaa := PetersenWireProjection.derive 3 pc34w69 pc34w71 rfl rfl
private theorem pc34w75 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w76 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w74 : PetersenPackedPin.project extra34 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xfafaaaaafafaaaaafafaaaaafafaaaaa := PetersenWireProjection.derive 0 pc34w75 pc34w76 rfl rfl






private theorem pc0w81 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w85 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w84 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w81 pc0w85 rfl rfl




private theorem pc0w91 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl


private theorem pc29w92 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl

private theorem pc29w97 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl

private theorem pc29w98 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w96 : PetersenPackedPin.project extra29 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 0 pc29w97 pc29w98 rfl rfl




private theorem pc2w104 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc29w106 : PetersenPackedPin.project extra29 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccccccccccccccc0000000000000000 := PetersenWireProjection.derive 0 stored155 stored156 rfl rfl
private theorem pc29w105 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w92 pc29w106 rfl rfl
private theorem pc0w107 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl




private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w114 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w113 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w114 stored35 rfl rfl




private theorem pc26w120 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w121 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w119 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffaaaaaaaaffffffffeeeeeeeeffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w120 pc26w121 rfl rfl
private theorem pc26w122 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w120 stored2 rfl rfl
private theorem pc30w124 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w123 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffff0f0f0f0fffffffffcfcfcfcfffffffff0f0f0f0 : BitVec 256) = 0xfaaafaaafaaafaaafaaafaaafaaafaaa := PetersenWireProjection.derive 3 pc30w16 pc30w124 rfl rfl
private theorem pc30w125 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xfaaafaaafaaafaaafaaafaaafaaafaaa := PetersenWireProjection.derive 3 pc30w16 stored10 rfl rfl
private theorem pc0w127 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl
private theorem pc0w126 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w127 stored51 rfl rfl
private theorem pc3w128 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl


private theorem pc37w129 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl


private theorem pc37w134 : PetersenPackedPin.project extra37 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored65 stored71 rfl rfl
private theorem pc37w133 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w134 stored66 rfl rfl




private theorem pc37w140 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w129 pc37w134 rfl rfl




private theorem pc69w143 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored99 stored100 rfl rfl
private theorem pc69w147 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored97 stored98 rfl rfl
private theorem pc69w146 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffffccccccccffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc69w147 pc69w143 rfl rfl




private theorem pc29w153 : PetersenPackedPin.project extra29 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0000000000000000 := PetersenWireProjection.derive 2 stored153 stored155 rfl rfl
private theorem pc29w152 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w153 pc29w98 rfl rfl
private theorem pc26w154 : PetersenPackedPin.project extra26 (0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w39 stored2 rfl rfl
private theorem pc30w155 : PetersenPackedPin.project extra30 (0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 pc30w50 stored10 rfl rfl
private theorem pc34w156 : PetersenPackedPin.project extra34 (0xffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc34w71 stored18 rfl rfl
private theorem pc3w157 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc26w158 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w39 stored1 rfl rfl
private theorem pc30w159 : PetersenPackedPin.project extra30 (0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 pc30w50 stored9 rfl rfl
theorem b3_3234 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3234 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(0,true),(1,true))] s3_3234 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w2 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3235 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3235 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(0,true),(3,true))] s3_3235 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfaf0faf0faf0faf0faf0faf0faf0faf0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w10 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3236 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3236 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,true)),(false,(0,true),(3,true))] s3_3236 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w12 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3237 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3237 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(3,true))] s3_3237 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3238 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3238 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(0,true)),(false,(0,false),(4,true))] s3_3238 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w14 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3239 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3239 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(0,true),(6,true))] s3_3239 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff000f000fffffffff000f000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w15 rfl))))))))) (by decide +kernel)
theorem b3_3240 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3240 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(6,true),(4,true))] s3_3240 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w18 (PetersenWireProjection.cons pc30w17 rfl)))))))))) (by decide +kernel)
theorem b3_3241 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3241 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true))] s3_3241 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons pc30w19 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3242 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3242 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(0,true),(7,true))] s3_3242 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons pc30w21 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3243 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3243 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(7,true),(0,true))] s3_3243 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffff000f000f000f000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons pc30w22 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3244 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3244 := by
  apply PetersenIndexedNode.close (bank := [s4_2345,a5769,a5770,s4_2900,a5771,s4_217,a5739,s4_2886,s4_771,a5772,a5773,s4_2885,a5774,a5775,a5776,s4_2904,a5777,a5778,a5779,a5780,a5781,a5782,s4_1578,a5783,a5784,a5785,a4820,a5786,a5787,a5788,a5789,a5790,a5791,a4760,a5792,a5793,a5794,a4528,a5795,a5796]) (PetersenIndexedNode.reasons 256 17 432 0x622210808840484046141210118888c28242222101084044202703040099242484048012a1011c0c1002770302101200488404614140088c44442028010908098505002361411080a00404202501008405400084045040280014040a08050102101042022101800e8840442024202800e1080a003f001e21111080842022101800d08404420300195141185060036a282514140060420221014808141012000840448402400120209080480821010a0808404280824200a0004202282014000a020504028081080921004202800b14100a081001538301c182002e7060383040050a08050401888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840424040a08090004202242012000901048402404108085040420280090a0805041001134301a18200266860343040040504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0442026260108089818c4c02406108080c0406028007018080c05000d434121a0a001e86824341400300c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800480c04060284048004210120017000a48092101006020301210100c04840048082120108008404424021011202006020301800300c0406030005313018982000e626031304001006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c1210110a0a83824202a101006040302248480c080604420230b0108089212616024049080806040302800100c080605000130b0185820006616030b04000006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2345 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1220 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1578 theta)
    · exact b4_2900 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2711 theta)
    · exact b4_217 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_505 theta)
    · exact b4_2886 theta
    · exact b4_771 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_771 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2885 theta)
    · exact b4_2885 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2422 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1218 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1760 theta)
    · exact b4_2904 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2422 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1218 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1760 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2904 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2345 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1220 theta)
    · exact b4_1578 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2900 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2711 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_217 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_505 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2886 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_771 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_771 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2885 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2885 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2711 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_505 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_217 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2886 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2711 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_505 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_217 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2886 theta)
theorem b3_3245 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3245 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3245 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w28 (PetersenWireProjection.cons pc2w25 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_3246 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3246 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false)),(false,(0,true),(5,true))] s3_3246 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaffff0000ffff0000,0xffffaaaaffffaaaaffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w42 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3247 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3247 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(0,false)),(false,(0,true),(4,true))] s3_3247 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w51 (PetersenWireProjection.cons pc30w48 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3248 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3248 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(6,false)),(false,(0,true),(1,true))] s3_3248 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w60 (PetersenWireProjection.cons pc32w54 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3249 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3249 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,false)),(false,(0,true),(1,true))] s3_3249 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafaaaaafafaaaaafafaaaaafafaaaaa,0xfafaaaaafafaaaaafafaaaaafafaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w74 (PetersenWireProjection.cons pc34w68 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3250 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3250 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3250 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w84 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w81 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_3251 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3251 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3251 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xffff0000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w84 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w91 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_3252 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3252 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3252 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w84 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3253 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3253 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3253 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w92 rfl)))))))))) (by decide +kernel)
theorem b3_3254 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3254 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3254 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w28 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w104 rfl)))))))))) (by decide +kernel)
theorem b3_3255 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3255 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3255 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w96 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w105 rfl)))))))))) (by decide +kernel)
theorem b3_3256 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3256 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3256 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w84 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w107 rfl)))))))))) (by decide +kernel)
theorem b3_3257 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3257 := by
  apply PetersenIndexedNode.close (bank := [s4_2346,s4_1304,s4_1303,s4_1302,a5797,a5798,a5799,s4_2901,s4_2714,a5800,a4851,a5638,a5801,a5802,a5803,a5804,a5805,a5806,a5807,a5808,a5809,a5810,a5811,a5812,a5813,a5814,a5815,a5816,a5817,a5818,a5819,a5820,a5821,a5822,a5823,a5824,a5825,a5826,a5827,s4_1580,s4_3169,s4_3168,a5828,a5829,s4_407,s4_403,a5537,a5540,a5830,s4_2891,s4_970,a5831,a5832,s4_2890,a5833,a4779,a4833,a5834,a5835,a5836,a5837,a5838,s4_533,a5839,a5840,s4_2968,a5841,s4_2889]) (PetersenIndexedNode.reasons 256 17 432 0x622212021880884046444210118888c888422221010901084048020400fd40408404801f21012008700428020a1012007a8404801cc00e084044808801b9080a0079003b801d12022006c480880198840442028404801921012006b0034421221010420221013818084044202480830a098404e0606141281812020420221018017084044203002d801628202006300308017c00ac420221014808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808801394100a08100268012c00920055002980144008ca08050401888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840424040a080900050102420120009010484024041404050405010800f8a0805041001e800ec00720045002180104006c504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c040602800b818080c050016800ac005200350019800c4004c0c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301800800c04060248088007920220025001124051202006020301800580c040603000a800490902001d000d80064002006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b0120209212616024049202006040302800200c0806050003800140006000f00068002c000006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2346 theta
    · exact b4_1304 theta
    · exact b4_1303 theta
    · exact b4_1302 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1580 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3169 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_3168 theta)
    · exact b4_2901 theta
    · exact b4_2714 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_407 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_403 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_533 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2968 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2889 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2891 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_970 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_970 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2890 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2890 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2346 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1304 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1303 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1302 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1580 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3169 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3168 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2901 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2346 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1304 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1303 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1302 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1580 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3169 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3168 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2901 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2346 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1304 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1303 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1302 theta)
    · exact b4_1580 theta
    · exact b4_3169 theta
    · exact b4_3168 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2901 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2714 theta)
    · exact b4_407 theta
    · exact b4_403 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_533 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2968 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2889 theta)
    · exact b4_2891 theta
    · exact b4_970 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_970 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2890 theta)
    · exact b4_2890 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2714 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_533 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_403 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_407 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2968 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2891 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2889 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2714 theta)
    · exact b4_533 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_403 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_407 theta)
    · exact b4_2968 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2891 theta)
    · exact b4_2889 theta
theorem b3_3258 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3258 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3258 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w113 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_3259 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3259 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s3_3259 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaa0000aaaa0000,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w122 (PetersenWireProjection.cons pc26w119 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3260 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3260 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false)),(false,(0,true),(1,true))] s3_3260 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfaaafaaafaaafaaafaaafaaafaaafaaa,0xfaaafaaafaaafaaafaaafaaafaaafaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w125 (PetersenWireProjection.cons pc30w123 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3261 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3261 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3261 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w126 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w81 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_3262 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3262 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3262 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w126 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3263 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3263 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3263 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w113 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w128 rfl)))))))))) (by decide +kernel)
theorem b3_3264 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3264 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_3264 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons pc37w133 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w129 rfl)))))))))) (by decide +kernel)
theorem b3_3265 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3265 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_3265 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons pc37w133 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w140 rfl)))))))))) (by decide +kernel)
theorem b3_3266 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3266 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s3_3266 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0x0,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w146 (PetersenWireProjection.cons pc69w143 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl)))))))))) (by decide +kernel)
theorem b3_3267 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3267 := by
  apply PetersenIndexedNode.close (bank := [s4_2348,a5842,a5843,s4_2902,a4066,s4_97,a5844,s4_2896,s4_777,a5845,a5846,s4_2895,a5847,a5848,a5849,s4_2905,a5850,a5851,a5852,a5853,a5854,a5855,s4_1584,a5856,a4077,a4076,a5857,a5858,a5859,a5860,a5861,a5862,a5863,a4796,a5864,a5865,a5866,a4546,a5867,a5868]) (PetersenIndexedNode.reasons 256 17 432 0x622212021880884046141210118888c28242222101090108404703040099242484048012a1011c0c100277030210120048840461414008884044808801090809850500236141120220040480870300840442028404514121011c0c0a28242122101042022101800e8840442024808800e12022003f001e28181202042022101800d08404420300195141185060036a282514140060420221014808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808800b14100a081001538301c182002e7060383040050a08050401888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840424040a08090005010242012000901048402404140405040501080090a0805041001134301a18200266860343040040504028201404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c0406028007018080c05000d434121a0a001e86824341400300c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800480c04060284048004210120017000a48092101006020301614100c04060248083130120218504626024051202006020301800300c0406030005313010902000e626031304001006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c1210110a0a83824202a101006040302248480c080604480830b0120209212616024049202006040302800100c080605000130b0185820006616030b04000006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2348 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1196 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1584 theta)
    · exact b4_2902 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2723 theta)
    · exact b4_97 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_546 theta)
    · exact b4_2896 theta
    · exact b4_777 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_777 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2895 theta)
    · exact b4_2895 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2447 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1184 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1793 theta)
    · exact b4_2905 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2447 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1184 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1793 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2905 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2348 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1196 theta)
    · exact b4_1584 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2902 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2723 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_546 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2896 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_777 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_777 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2895 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2895 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2723 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_546 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_97 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2896 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2723 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_546 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_97 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2896 theta)
theorem b3_3268 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3268 := by
  apply PetersenIndexedNode.close (bank := [a5869,a5870,a5871,a5872,s4_2021,a5873,s4_2894,s4_97,a5874,a4676]) (PetersenIndexedNode.reasons 256 17 173 0x84044202108088404c444614121112001100078004c0019c0c0c4447030311118504c8886141322204202a2825141084044202c4447030084044202c28280028840442022a0a1505084060008504028204000ca080d04048401410121005040282024200a0807060383014100620221011088884045040484024200a0805040c84024600a0805040484024200a08050402a2215110a080500028001404084045040382014180a0800c0484804240018080c04c4406222018080c04c480426001809090006020301212004a0221011082884040c0416020309018080c040e0203050180a00046260313040004c4c0c4448000311118504626031303222006020301150508404541421013130141012504504015110a080544428200301199800c046260018118580c2c00302018131111888a0302018118580c2c00302109000c080604212010800840042020302018104c0806240302018102c080614030201810180842480302109000c0806042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_3010 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2737 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1094 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2356 theta)
    · exact b4_2021 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_3007 theta)
    · exact b4_2894 theta
    · exact b4_97 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_155 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2918 theta)
theorem b3_3269 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3269 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3269 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons pc29w98 (PetersenWireProjection.cons pc29w152 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3270 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3270 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(7,true))] s3_3270 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons pc26w154 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3271 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3271 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,true)),(false,(0,true),(1,true))] s3_3271 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w2 (PetersenWireProjection.cons pc30w155 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3272 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3272 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,true)),(false,(0,true),(3,true))] s3_3272 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w76 (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3273 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3273 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3273 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w157 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_3274 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3274 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true)),(false,(5,true),(1,true))] s3_3274 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w158 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3275 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3275 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true)),(false,(4,true),(3,true))] s3_3275 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w2 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w159 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
