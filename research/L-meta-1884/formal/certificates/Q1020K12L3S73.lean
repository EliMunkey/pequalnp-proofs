import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S12
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S20
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S39
import Q1020K12L4S41
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc0w0 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl





private theorem pc0w8 : PetersenPackedPin.project cycle0 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33003300 := PetersenWireProjection.derive 1 stored49 stored55 rfl rfl
private theorem pc0w10 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w7 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w8 pc0w10 rfl rfl




private theorem pc30w13 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl




private theorem pc30w20 : PetersenPackedPin.project extra30 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff00000000 := PetersenWireProjection.derive 1 stored8 stored14 rfl rfl
private theorem pc30w22 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w19 : PetersenPackedPin.project extra30 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xff00ff00fff0fff0ff00ff00fff0fff0 := PetersenWireProjection.derive 2 pc30w20 pc30w22 rfl rfl




private theorem pc117w25 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored122 stored123 rfl rfl




private theorem pc117w33 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored123 stored124 rfl rfl
private theorem pc117w32 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc117w33 stored122 rfl rfl
private theorem pc117w35 : PetersenPackedPin.project extra117 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored121 stored124 rfl rfl
private theorem pc117w31 : PetersenPackedPin.project extra117 (0xccccccccccccccccccccccccccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc117w32 pc117w35 rfl rfl









private theorem pc26w43 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w47 pc26w48 rfl rfl
private theorem pc26w50 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeffffffffeeeeeeeeeeeeeeeeeeeeeeeeffffffffeeeeeeee : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w50 pc26w43 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl
private theorem pc30w52 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w54 : PetersenPackedPin.project extra30 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored9 stored14 rfl rfl
private theorem pc30w55 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w53 : PetersenPackedPin.project extra30 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 2 pc30w54 pc30w55 rfl rfl
private theorem pc30w57 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored9 stored10 rfl rfl
private theorem pc30w56 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfffffffffcfcfcfcfcfcfcfcfcfcfcfcfffffffffcfcfcfc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc30w57 pc30w52 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl






private theorem pc32w63 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl

private theorem pc32w68 : PetersenPackedPin.project extra32 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored25 stored29 rfl rfl
private theorem pc32w69 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl
private theorem pc32w67 : PetersenPackedPin.project extra32 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 pc32w68 pc32w69 rfl rfl

private theorem pc32w72 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 2 stored25 stored26 rfl rfl
private theorem pc32w71 : PetersenPackedPin.project extra32 (0xffccffccffccffccffffffffffccffccffccffccffccffccffffffffffccffcc : BitVec 256) = 0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc32w72 pc32w63 rfl rfl
private theorem pc30w73 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl





private theorem pc34w78 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl


private theorem pc34w84 : PetersenPackedPin.project extra34 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 1 stored17 stored22 rfl rfl
private theorem pc34w85 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w83 : PetersenPackedPin.project extra34 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaafafaaaaafafaaaaafafaaaaafafa := PetersenWireProjection.derive 2 pc34w84 pc34w85 rfl rfl

private theorem pc34w88 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 2 stored17 stored18 rfl rfl
private theorem pc34w87 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffffffffffccccffffccccffffccccffffffffffffcccc : BitVec 256) = 0xaaaafafaaaaafafaaaaafafaaaaafafa := PetersenWireProjection.derive 3 pc34w88 pc34w78 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc32w90 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl




private theorem pc2w94 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl



private theorem pc2w101 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w100 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w101 pc2w94 rfl rfl

private theorem pc30w103 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc32w104 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc34w105 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl
private theorem pc26w106 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl



private theorem pc29w108 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl




private theorem pc29w116 : PetersenPackedPin.project extra29 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored155 stored154 rfl rfl
private theorem pc29w117 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl
private theorem pc29w115 : PetersenPackedPin.project extra29 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 2 pc29w116 pc29w117 rfl rfl

private theorem pc32w119 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc34w120 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc2w121 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
private theorem pc29w122 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w117 stored155 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc29w124 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl
private theorem pc29w126 : PetersenPackedPin.project extra29 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 stored155 stored156 rfl rfl
private theorem pc29w125 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w124 pc29w126 rfl rfl
private theorem pc30w127 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc32w128 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc34w129 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored16 stored19 rfl rfl
private theorem pc2w130 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl


private theorem pc74w131 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl





private theorem pc74w139 : PetersenPackedPin.project extra74 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored114 stored119 rfl rfl
private theorem pc74w141 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc74w138 : PetersenPackedPin.project extra74 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc74w139 pc74w141 rfl rfl



private theorem pc115w143 : PetersenPackedPin.project extra115 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored201 stored202 rfl rfl





private theorem pc115w151 : PetersenPackedPin.project extra115 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x4444444444444444 := PetersenWireProjection.derive 1 stored203 stored207 rfl rfl
private theorem pc115w150 : PetersenPackedPin.project extra115 (0xccccccccccccccccffffffffffffffffcccccccc00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc115w143 pc115w151 rfl rfl

theorem b3_3066 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3066 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3066 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w7 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w0 rfl))))))))) (by decide +kernel)
theorem b3_3067 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3067 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(5,true)),(false,(0,true),(4,true))] s3_3067 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00fff0fff0ff00ff00fff0fff0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w19 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3068 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3068 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_3068 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xcccccccccccccccc,0xffffffffffffffff,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons pc117w31 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons stored123 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w25 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_3069 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3069 := by
  apply PetersenIndexedNode.close (bank := [s4_2281,s4_2280,s4_2279,a5704,a5705,a5706,a5707,s4_2858,s4_3,a5708,a4708,a5709,a5710,s4_738,a5711,a5712,a5713,a5714,a5715,a5716,a5717,a5718,s4_2878,a5719,s4_1531,a5720,a5721,s4_2640,a4815,a5638,s4_2898,a5640,a4759,a5642,s4_2912,a4339,s4_1179,a5722,s4_2926,a5723,s4_2820]) (PetersenIndexedNode.reasons 256 17 426 0x2004e42022101210118504c202801430a088504840421011080944442a0a5000210114100a00051112820144448404150521010c4442a0a310110808c282420231111850484444202150510809202050404800210112100900048082420120208404282021010a4249080290110808a080420229091410084244202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a8291818282046022101191808404460632301081884041410210109414282025011080890804202250512100841442021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a081080806024200240410900840042022120108089010030101808e8680602030110809898042023a1a31300e0684202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092425002549092101200488404490940099242484048011a101084050021210132222004048082101400888404c888800fb22205415001d1080a8202003821011505400785414a080800da8200a081001928202420200309080282040068a0809080800ba4200504100151410323020028c8c01410400585040c8c08009b23000c050011030121202002084800301400480c0484808007a120124242624490921012001a8404490940039242484041312210108404262421011c0c08480622021011090084047030131212028541442401505185044c4826241505098905014614121200a029250426241312141006c68362449410d8d04c6850401312098905444262415100a082001628201511400305044282013120a0800c0442400301212004c4826200301098900c048480212010902001500090180c00204c480301428280c080604840441c120c090a0a83824202a10100604030264c480c080604420230b0108099312616010b0108080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030280034001600090003018100c0a000e030201814000a0003000021a08848042402624018100c088682030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2281 theta
    · exact b4_2280 theta
    · exact b4_2279 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_495 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1750 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1749 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1748 theta)
    · exact b4_2858 theta
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_156 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_155 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1485 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2935 theta)
    · exact b4_738 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2936 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2314 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1669 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_487 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2865 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2390 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1544 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_447 theta)
    · exact b4_2878 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2405 theta)
    · exact b4_1531 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_415 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2884 theta)
    · exact b4_2640 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_836 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_533 theta)
    · exact b4_2898 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2694 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1005 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_505 theta)
    · exact b4_2912 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_1179 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_704 theta)
    · exact b4_2926 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_768 theta)
    · exact b4_2820 theta
theorem b3_3070 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3070 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3070 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3071 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3071 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3071 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3072 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3072 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3072 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3073 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3073 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3073 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w52 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3074 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3074 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3074 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w56 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3075 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3075 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3075 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w58 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3076 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3076 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3076 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w63 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3077 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3077 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3077 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w71 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3078 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3078 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3078 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w73 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3079 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3079 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3079 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3080 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3080 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_3080 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w78 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3081 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3081 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_3081 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w87 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3082 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3082 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3082 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w89 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3083 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3083 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3083 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons pc32w90 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3084 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3084 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3084 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3085 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3085 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3085 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w100 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w94 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_3086 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3086 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3086 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w103 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3087 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3087 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3087 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3088 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3088 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_3088 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w105 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3089 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3089 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3089 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w106 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_3090 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3090 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3090 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w115 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w108 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3091 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3091 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3091 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w13 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_3092 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3092 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3092 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w119 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_3093 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3093 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_3093 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w120 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_3094 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3094 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3094 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w100 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w121 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_3095 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3095 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3095 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w115 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w122 (PetersenWireProjection.cons stored153 rfl)))))))))) (by decide +kernel)
theorem b3_3096 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3096 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3096 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w100 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_3097 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3097 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_3097 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w123 rfl)))))))))) (by decide +kernel)
theorem b3_3098 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3098 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3098 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w115 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w124 rfl)))))))))) (by decide +kernel)
theorem b3_3099 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3099 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_3099 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons pc29w115 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w125 rfl)))))))))) (by decide +kernel)
theorem b3_3100 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3100 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3100 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff0aff0aff0aff0aff0aff0aff0aff0a,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w127 rfl)))))))))) (by decide +kernel)
theorem b3_3101 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3101 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,true)),(false,(0,true),(1,true))] s3_3101 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaffffaaaaffffaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons pc32w67 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w128 rfl)))))))))) (by decide +kernel)
theorem b3_3102 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3102 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s3_3102 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaafafaaaaafafaaaaafafaaaaafafa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w83 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w129 rfl)))))))))) (by decide +kernel)
theorem b3_3103 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3103 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3103 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w100 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 (PetersenWireProjection.cons pc2w130 rfl)))))))))) (by decide +kernel)
theorem b3_3104 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3104 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_3104 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w138 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w131 rfl)))))))))) (by decide +kernel)
theorem b3_3105 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3105 := by
  apply PetersenIndexedNode.close (bank := [s4_2296,a5724,a5725,s4_2860,s4_2771,s4_204,a5726,s4_2832,a5727,a5728,a5729,a5730,a5731,a5732,a5733,s4_2880,a5734,s4_1535,a5735,a5736,a5737,a5738,a5739,a5740,s4_2666,a5741,a5742,a5647,a5743,s4_528,a5642,a5744,a5745,s4_2830,a5746,a5747]) (PetersenIndexedNode.reasons 256 17 432 0x6222108088404a0206141310118888c282622228080840442025010185054040c4445040381014040a080501031110c2828424311128200c202420230a098404c4446141311110809410042025818141016040a02048402808160609080501828080a080a020280824200a0004202282014000a020504028081080921004202801114100a080614138301c10200467060283018504a080504080100a0805040a0206460280820042c8c02460280805040282024040a0809000420224201200090104840240410808504042025444121009080614114100a08151102820141018504908048404c440a080504050401c180e08131103830141814100504028205212018080c04a020424028081484884805012280800c0406022606018080c0442026260108089818c4c02406108080c04060232a2818080c046141131109888ca8a26221311185040c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406025010400790808c444800ea10114041001f5010311120038c444311140068c4444202800c90808c445001b31111080a0030420250404005842026141800a884054101001750401850600286141484040049210050408008941012101001348401410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a00100602511100c040602a02041c0a80814444838150112808006020301210100c04840048082120108008404424021011202006020301514100c04060261411312098914504262413121850406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800300c0406030005131209892000e26241312400100602030162a280c080604a02041c1280818a8a83826222a808006040302248480c080604420230b010808921261602404908080604030230a080c080604a080109008480c28221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b02252410920180806040302800100c0806050001109008482000621201090400000604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2296 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1219 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1755 theta)
    · exact b4_2860 theta
    · exact b4_2771 theta
    · exact b4_204 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_222 theta)
    · exact b4_2832 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2296 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1755 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1219 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2860 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2411 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1535 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1217 theta)
    · exact b4_2880 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2411 theta)
    · exact b4_1535 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1217 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2880 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2629 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_528 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_505 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2888 theta)
    · exact b4_2666 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1155 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1221 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2918 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2629 theta)
    · exact b4_528 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_505 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2888 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1487 theta)
    · exact b4_2830 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1487 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2830 theta)
theorem b3_3106 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3106 := by
  intro m le c
  apply rejects_sound extra115 i6 5 tgt small115 hot115 [] s3_3106 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0xffffffff00000000,0x0,0xcccccccccccccccc,0x0,0x0] (PetersenWireProjection.cons stored208 (PetersenWireProjection.cons stored207 (PetersenWireProjection.cons pc115w150 (PetersenWireProjection.cons stored206 (PetersenWireProjection.cons stored205 (PetersenWireProjection.cons stored204 (PetersenWireProjection.cons stored202 (PetersenWireProjection.cons stored203 (PetersenWireProjection.cons stored201 (PetersenWireProjection.cons pc115w143 rfl)))))))))) (by decide +kernel)
theorem b3_3107 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3107 := by
  apply PetersenIndexedNode.close (bank := [s4_2298,a5748,a5749,s4_2861,s4_3,a5750,a5726,a5751,a5752,a5753,a5754,a5755,a5756,a5757,a5758,a5759,s4_2881,a5760,s4_1537,a5761,a5762,a5737,a5763,a5739,a5764,s4_2668,a5765,a5766,s4_2926,a5743,s4_830,a5642,a4352]) (PetersenIndexedNode.reasons 256 17 426 0x1888842022101248498504c202622230a098888921221011080940402a0a5101248494100a2025010282014040921215050a828c4442a0a308090808c28261013111185048444420215051080924245040490128081210092024909242012424a020282028080a0209080280010808a0805000280814100a0204202484010808743450401d050a828e0c02a0a1d0d1c18054342a0a28200a829343428204d0924849918092124d0d32301243492121410248489010282024001080890804800240412100901042021410108085414484015011850450402a0215050a0805414614124201210131102820141014100706038204c440e0c05060504014100a081484806020301248490900860252122120140489212030101808981806020301108098980420226063130090184202030101808ca8a060203010a8284c44260232a2898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092425001f420231112003c84044909400812424c444800eb11108405001b2101120220034480821014007084044808800c9202054150017108098506002c210115054006054146141800a985052101001348401410200245040484040051210050408008941005041000f141012102001c4840141040040504048408006921000c05000b0301313020014c4c00301400300c04c4c08004b1301242426244909280810702a020490920e052024a02013122404884042624210112022000e480821014002084044808131212020541483811505185044c4826241505098905014614141c08a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0483810301212004c4826200301098900c04848041c0a1202000d00050180c00104c48030162a280c080604921241c120c098a8a83826222a484806040302248480c080604420230b010808921261602404908080604030230a080c0806042a0a109008c08c282212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b02252410920180806040302800118580c2c10001018100c0a00060302018140000c2c0616041c08848042402624018100c090702030201810989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2298 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_856 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1757 theta)
    · exact b4_2861 theta
    · exact b4_3 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_223 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_222 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_967 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2948 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2298 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1757 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_856 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2861 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2413 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1537 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_434 theta)
    · exact b4_2881 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2413 theta)
    · exact b4_1537 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_434 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2881 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2629 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_830 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_505 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2898 theta)
    · exact b4_2668 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1179 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_960 theta)
    · exact b4_2926 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2629 theta)
    · exact b4_830 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_505 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2898 theta)
end Orbits1020Cost12
