import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S5
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S10
import Q1020K12L4S13
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S18
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S27
import Q1020K12L4S54
import Q1020K12L4S56
import Q1020K12L4S60
import Q1020K12L4S62
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc30w7 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl

private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w9 : PetersenPackedPin.project extra30 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff000000000fff0fff0 := PetersenWireProjection.derive 1 pc30w10 stored8 rfl rfl







private theorem pc34w18 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored19 stored22 rfl rfl

private theorem pc34w21 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w20 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w21 stored16 rfl rfl







private theorem pc3w29 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w32 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w31 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 1 pc3w32 stored33 rfl rfl







private theorem pc0w40 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w43 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w42 : PetersenPackedPin.project cycle0 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 pc0w43 stored49 rfl rfl
private theorem pc3w44 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl







private theorem pc1w52 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored63 rfl rfl

private theorem pc1w55 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl
private theorem pc1w54 : PetersenPackedPin.project cycle1 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 1 pc1w55 stored57 rfl rfl







private theorem pc73w63 : PetersenPackedPin.project extra73 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 1 stored129 stored135 rfl rfl
private theorem pc73w65 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w62 : PetersenPackedPin.project extra73 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w63 pc73w65 rfl rfl

private theorem pc73w67 : PetersenPackedPin.project extra73 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w65 stored129 rfl rfl








private theorem pc26w74 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc26w78 stored0 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored11 stored13 rfl rfl
private theorem pc30w80 : PetersenPackedPin.project extra30 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored10 stored13 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0f0f0f0f0f0f0f0f0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc30w10 stored13 rfl rfl
private theorem pc30w82 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored8 stored13 rfl rfl
private theorem pc30w85 : PetersenPackedPin.project extra30 (0x3030303030303030303030303030303030303030303030303030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored13 stored14 rfl rfl
private theorem pc30w84 : PetersenPackedPin.project extra30 (0x303030303030303000000000000000003030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w85 stored9 rfl rfl
private theorem pc30w83 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000003030303030303030 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc30w84 pc30w82 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored13 stored14 rfl rfl
private theorem pc30w87 : PetersenPackedPin.project extra30 (0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 pc30w88 stored9 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored13 rfl rfl
private theorem pc30w86 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffcfcfcfcfcfcfcfc : BitVec 256) = 0xfff0fff000000000fff0fff0 := PetersenWireProjection.derive 1 pc30w87 pc30w89 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored5 stored7 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored4 stored7 rfl rfl






private theorem pc32w96 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl


private theorem pc32w102 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w101 : PetersenPackedPin.project extra32 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc32w102 stored24 rfl rfl
private theorem pc30w103 : PetersenPackedPin.project extra30 (0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored12 stored13 rfl rfl
private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc73w106 : PetersenPackedPin.project extra73 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w65 stored131 rfl rfl
private theorem pc1w107 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl




private theorem pc116w113 : PetersenPackedPin.project extra116 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored107 stored111 rfl rfl
private theorem pc116w112 : PetersenPackedPin.project extra116 (0x333333330000000000000000000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc116w113 stored106 rfl rfl
private theorem pc116w115 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored105 stored107 rfl rfl
private theorem pc116w111 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff0000000000000000000000003333333300000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc116w112 pc116w115 rfl rfl




private theorem pc116w121 : PetersenPackedPin.project extra116 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored106 stored111 rfl rfl
private theorem pc116w120 : PetersenPackedPin.project extra116 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc116w121 stored105 rfl rfl
private theorem pc116w124 : PetersenPackedPin.project extra116 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored107 stored111 rfl rfl
private theorem pc116w123 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 pc116w124 stored106 rfl rfl
private theorem pc116w125 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored105 stored107 rfl rfl
private theorem pc116w122 : PetersenPackedPin.project extra116 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc116w123 pc116w125 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc30w127 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc1w128 : PetersenPackedPin.project cycle1 (0xffffffffffffffffcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w55 stored57 rfl rfl


private theorem pc29w129 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl

private theorem pc29w132 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl





private theorem pc29w139 : PetersenPackedPin.project extra29 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f := PetersenWireProjection.derive 1 pc29w132 stored153 rfl rfl
private theorem pc29w140 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w132 stored153 rfl rfl
private theorem pc26w141 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w74 stored1 rfl rfl
private theorem pc26w142 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl


private theorem pc41w143 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl






private theorem pc41w153 : PetersenPackedPin.project extra41 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored89 stored95 rfl rfl
private theorem pc41w152 : PetersenPackedPin.project extra41 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w153 stored91 rfl rfl
private theorem pc30w154 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored13 rfl rfl
private theorem pc41w155 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl
private theorem pc41w156 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w153 stored91 rfl rfl
theorem b3_1638 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1638 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1638 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w7 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1639 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1639 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(4,true)),(false,(7,true),(0,true))] s3_1639 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w20 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w18 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1640 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1640 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,false))] s3_1640 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0000,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w31 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w29 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1641 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1641 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(1,false))] s3_1641 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w42 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w40 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_1642 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1642 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(4,false))] s3_1642 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0000,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w31 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w44 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w32 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_1643 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1643 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1643 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0x0,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w54 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w52 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1644 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1644 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_1644 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w67 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons pc73w62 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_1645 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1645 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1645 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1646 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1646 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1646 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1647 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1647 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1647 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1648 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1648 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1648 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1649 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1649 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1649 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w82 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1650 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1650 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1650 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1651 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1651 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1651 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xfff0fff000000000fff0fff0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w86 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1652 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1652 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1652 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w90 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1653 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1653 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1653 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1654 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1654 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1654 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1655 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1655 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1655 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w101 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w96 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1656 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1656 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true)),(false,(6,true),(0,true))] s3_1656 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w103 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1657 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1657 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(4,true)),(false,(7,true),(0,true))] s3_1657 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w20 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1658 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1658 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1658 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1659 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1659 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_1659 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0x0,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w67 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons pc73w106 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_1660 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1660 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1660 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w54 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w107 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1661 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1661 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1661 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w120 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons pc116w111 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl)))))))))) (by decide +kernel)
theorem b3_1662 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1662 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1662 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons pc116w120 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored111 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w122 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 rfl)))))))))) (by decide +kernel)
theorem b3_1663 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1663 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1663 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1664 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1664 := by
  apply PetersenIndexedNode.close (bank := [s4_778,s4_1014,a4093,a4656,s4_2898,s4_1146,a4657,a4658]) (PetersenIndexedNode.reasons 256 17 173 0x4202420230a088404a0204202280810808420264441080991102a0a42022808108086202210110888840421011080a40012000901042021480884044212210114100e0c0706028200e82854142a1a1505230110808840c4202128088404420a2101121005040282024200a80854042a0a24200a0807040283014102100108008404030101808840484c00301212000c0406024240018084c0406220301018082c0406120301018081c04060a03012888108090007420210808c4c0420238191090084802a0a313010980c4c050404941141005444282015110a0800c04666003011898006048404420280c080604420230b000c0a000c030201814001406042302109000c0806041302018900c0806040b02018500c0806040602109200c0842400302018108481242484042101120208404c2828001c000a00090001150528a085414a282282024200a080908015110a080544428200301212000c048480131209890c4c1000001810848006042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_778 theta
    · exact b4_1014 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_19 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2752 theta)
    · exact b4_2898 theta
    · exact b4_1146 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1144 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1169 theta)
theorem b3_1665 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1665 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1665 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w127 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1666 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1666 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(1,true),(2,true))] s3_1666 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfcfcfcfc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0,0x0] (PetersenWireProjection.cons pc1w54 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w128 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b3_1667 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1667 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1667 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w78 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1668 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1668 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1668 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w139 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w132 (PetersenWireProjection.cons pc29w129 rfl)))))))))) (by decide +kernel)
theorem b3_1669 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1669 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1669 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w139 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w132 (PetersenWireProjection.cons pc29w140 rfl)))))))))) (by decide +kernel)
theorem b3_1670 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1670 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1670 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w141 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1671 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1671 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1671 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfff0fff0fff0fff0fff0fff0fff0fff0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w87 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1672 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1672 := by
  apply PetersenIndexedNode.close (bank := [s4_3,a4659,s4_1147,a4660,a4661,s4_1145]) (PetersenIndexedNode.reasons 256 17 170 0x140408404501021010840484046141108099110420215052101140408404108088404c40442022111108092000900048082101121005040282024200a404420221091080874142a0a150d0a82918088404420621012000a28201410400109404420221051080854042a021505121005040382014180a08108008400420201809090006020301212000c0442026260018080c0426020311018080c0416020309018080c040e0203050180944408404616021011070242402101109008404480a150518900541442402120141012504424015110a080544428200301119000c044240018121011080a0302800180c0806050002018110808c2c00302018108c0842400302018104c0806240302018102c080614030201810180842480302109000c08060421204909210120003000021011c0c08404c282150528a085414a282282024200a080908015110a080544428200301212000c0484801312098908480c2c001810848006042120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_3 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2793 theta)
    · exact b4_1147 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1145 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1147 theta)
    · exact b4_1145 theta
theorem b3_1673 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1673 := by
  apply PetersenIndexedNode.close (bank := [s4_452,a4662,a4663,s4_2529,s4_704,a4664,a4339,s4_2812,s4_865,a4665,a4666,a4667,a4668,s4_357,a4669,a4670,a4671,s4_275,a4672,a4673,s4_902,s4_222,a4545,a4105,a4674,s4_97,a4675,a4367,s4_3,a4676,s4_1159,s4_1134,a4677,a4678,s4_1157,a4679,s4_1163,a4680,a4681]) (PetersenIndexedNode.reasons 256 17 426 0x2004a420221012101185048404801330a0985048404210110809404021015000210114100a00050102820140408404108088404c4442101108090808c282420231111850484444202108088405202050404800210112100900048082420120208404282021010a4249080290110808a08042022909141008424420248401080862225040188088404e0c0210118889c18042222101282008405181828204602210119180840446063230108188404141021010941428202501108089080420225051210084144202141010808501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180a0046060203011080989804202801231301098042020301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a004242404180a101107028301801120e050702840421202101084048381210132220848042402101109008404c88841c09202854144240150508404c4c021011505189805414210121200840525044240212014102003e5040494140081210450402120109005444424015110a08117122820151122e245444282021200a0800c0442400301212008c8846400301119100c0484802120109010a0a0302018121011070484044282a0e09080a8404018100c0993120302018110808c2c0420264c498580c2c04202018100c084202030210800a0204240210010808848042022808018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090109000604030221a080c0806044240109008482003d001d490921012003884042101400688404c282800c920208405001b210130a0a0030c28215054005854142101800a884045415001715050840600282101282040048a08090808008a4200a0810013282024202002090801511400385444282080068a0805445000f15110a082001828200301400280c0484808004a12000c05000b0301212020010848021204001806028381800280c0484810007212020e0600088381018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_452 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_357 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2385 theta)
    · exact b4_2529 theta
    · exact b4_704 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_97 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2613 theta)
    · exact b4_2812 theta
    · exact b4_865 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_275 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2270 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2557 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_452 theta)
    · exact b4_357 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2385 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2529 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_865 theta)
    · exact b4_275 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2270 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2557 theta)
    · exact b4_902 theta
    · exact b4_222 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2692 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2832 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_704 theta)
    · exact b4_97 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2613 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2812 theta)
    · exact b4_3 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2918 theta)
    · exact b4_1159 theta
    · exact b4_1134 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1163 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_656 theta)
    · exact b4_1157 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1134 theta)
    · exact b4_1163 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_656 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1157 theta)
theorem b3_1674 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1674 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1674 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w77 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w142 rfl)))))))))) (by decide +kernel)
theorem b3_1675 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1675 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1675 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w152 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w143 rfl)))))))))) (by decide +kernel)
theorem b3_1676 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1676 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1676 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w154 rfl)))))))))) (by decide +kernel)
theorem b3_1677 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1677 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1677 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w152 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w155 rfl)))))))))) (by decide +kernel)
theorem b3_1678 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1678 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_1678 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w152 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w156 rfl)))))))))) (by decide +kernel)
theorem b3_1679 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1679 := by
  apply PetersenIndexedNode.close (bank := [a4682,s4_2530,s4_705,a4632,s4_1148,a4683,a4684,a4685,s4_101,a4686,s4_2925,a4636,s4_1155,s4_1159,a4687,a4688,s4_1135,a4689,a4690,a4658,a4691,a4678,a4692,s4_1164,s4_1153,a4693,a4694,a4695,a4696]) (PetersenIndexedNode.reasons 256 17 426 0x20039001b6202210108404420280069080884048404800d21011404021015000210105414a00050100a82854148404108088404c4442101108090808c282420231111850484444202108088405202050404800210112100900048082420120208404282021010a4249080290110808a08042022909141008424420248401080862225040188088404e0c0210118889c18042222101282008405181828204602210105444840446060a88908188404141021010941428202501108089080420225051210084144202141010808501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a081080900194200240400c0484004202018080c049010800c24042002c060203011080989804202800bb1301098042020301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c14282003010180a002b00144180a101107028301210120e048404c888616030a008404c2c021013222107028381150520e04541421018009084045415001315050840507022101494120e05250050408008141012505001148411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808007212000c05000f030121201070284804282884810a088404018100c090a0a03020181210104240840464c480c080604420230b0108099312616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b004240212080064002e00148404490921012001a9212490921012000484042101248488404c28280041202084050009210130a092424c202150524848541421015111084045414a2225101084052424210128202888944449080490924848a080921249012420144449202151124849242428204d0d2486854449a1a4d090a081242492120301248480c0484808003212000c0500070301212012424860280024000d2024838149092404a000a9212490920e0600048381018124848060421208000084800605000101810848124248302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_358 theta)
    · exact b4_2530 theta
    · exact b4_705 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2614 theta)
    · exact b4_1148 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1160 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_276 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2558 theta)
    · exact b4_101 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2813 theta)
    · exact b4_2925 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2897 theta)
    · exact b4_1155 theta
    · exact b4_1159 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1138 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1167 theta)
    · exact b4_1135 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1165 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_571 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1169 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_657 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_656 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1136 theta)
    · exact b4_1164 theta
    · exact b4_1153 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1140 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1150 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1059 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1060 theta)
end Orbits1020Cost12
