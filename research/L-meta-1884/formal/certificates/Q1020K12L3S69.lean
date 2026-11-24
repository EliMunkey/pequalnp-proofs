import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S2
import Q1020K12L4S9
import Q1020K12L4S12
import Q1020K12L4S22
import Q1020K12L4S23
import Q1020K12L4S24
import Q1020K12L4S28
import Q1020K12L4S30
import Q1020K12L4S31
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S53
import Q1020K12L4S54
import Q1020K12L4S55
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S66
import Q1020K12L4S67
import Q1020K12L4S68
import Q1020K12L4S69
import Q1020K12L4S70
import Q1020K12L4S71
import Q1020K12L4S74
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc0w1 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl

private theorem pc0w4 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl



private theorem pc0w9 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl




private theorem pc3w13 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl

private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w13 stored34 rfl rfl
private theorem pc3w17 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl



private theorem pc3w21 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w23 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored33 stored35 rfl rfl
private theorem pc0w24 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
private theorem pc3w26 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w25 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w26 stored36 rfl rfl
private theorem pc0w28 : PetersenPackedPin.project cycle0 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored52 rfl rfl
private theorem pc0w29 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored52 rfl rfl
private theorem pc0w27 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 2 pc0w28 pc0w29 rfl rfl
private theorem pc3w31 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w30 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w31 stored36 rfl rfl
private theorem pc0w32 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w33 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w9 stored52 rfl rfl




private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl

private theorem pc26w37 : PetersenPackedPin.project extra26 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w38 stored3 rfl rfl



private theorem pc0w44 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffff00 := PetersenWireProjection.derive 3 stored49 stored51 rfl rfl
private theorem pc3w47 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w47 stored33 rfl rfl
private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w46 pc3w21 rfl rfl


private theorem pc74w50 : PetersenPackedPin.project extra74 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored113 stored115 rfl rfl

private theorem pc74w49 : PetersenPackedPin.project extra74 (0xffffffffffffffff0000000000000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w50 stored114 rfl rfl




private theorem pc74w59 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl
private theorem pc74w58 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w59 stored113 rfl rfl
private theorem pc74w60 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl
private theorem pc74w57 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w58 pc74w60 rfl rfl

private theorem pc3w63 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w31 stored33 rfl rfl
private theorem pc3w62 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w63 pc3w21 rfl rfl
private theorem pc3w64 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w26 pc3w21 rfl rfl
private theorem pc3w65 : PetersenPackedPin.project cycle3 (0xffffffffffffffff0000000000000000ffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w26 stored34 rfl rfl
private theorem pc3w66 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl







private theorem pc1w75 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w76 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xc0c0c0c0 := PetersenWireProjection.derive 0 stored58 stored63 rfl rfl
private theorem pc1w74 : PetersenPackedPin.project cycle1 (0xcccccccccccccccc0000000000000000cccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w75 pc1w76 rfl rfl

private theorem pc3w78 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl






private theorem pc30w85 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl

private theorem pc30w84 : PetersenPackedPin.project extra30 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 3 pc30w85 stored13 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored13 stored14 rfl rfl
private theorem pc30w88 : PetersenPackedPin.project extra30 (0xccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 3 pc30w85 pc30w89 rfl rfl






private theorem pc32w96 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl

private theorem pc32w95 : PetersenPackedPin.project extra32 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w96 stored28 rfl rfl

private theorem pc32w101 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored28 stored29 rfl rfl
private theorem pc32w100 : PetersenPackedPin.project extra32 (0xcccccccccccccccccc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc32w96 pc32w101 rfl rfl



private theorem pc111w105 : PetersenPackedPin.project extra111 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored177 stored179 rfl rfl

private theorem pc111w107 : PetersenPackedPin.project extra111 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored178 stored179 rfl rfl
private theorem pc111w104 : PetersenPackedPin.project extra111 (0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc111w105 pc111w107 rfl rfl




private theorem pc111w115 : PetersenPackedPin.project extra111 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored178 stored183 rfl rfl
private theorem pc111w114 : PetersenPackedPin.project extra111 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc111w115 stored177 rfl rfl
private theorem pc111w116 : PetersenPackedPin.project extra111 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored179 stored183 rfl rfl
private theorem pc111w113 : PetersenPackedPin.project extra111 (0xcccccccccccccccccccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc111w114 pc111w116 rfl rfl

private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc000000000000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w21 stored33 rfl rfl
private theorem pc3w118 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w119 pc3w31 rfl rfl
private theorem pc74w121 : PetersenPackedPin.project extra74 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xc0c0c0c0c0c0c0c0 := PetersenWireProjection.derive 0 stored113 stored115 rfl rfl
private theorem pc74w120 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w121 stored114 rfl rfl
private theorem pc74w123 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc74w59 stored113 rfl rfl
private theorem pc74w122 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccc00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w123 pc74w60 rfl rfl
private theorem pc3w125 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w31 stored33 rfl rfl
private theorem pc3w124 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w125 pc3w21 rfl rfl
private theorem pc3w126 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w21 stored35 rfl rfl
private theorem pc3w127 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w21 pc3w31 rfl rfl
private theorem pc3w128 : PetersenPackedPin.project cycle3 (0xffffffffffffffffcccccccc00000000ffffffffffffffffcccccccc00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc3w31 stored34 rfl rfl



private theorem pc76w131 : PetersenPackedPin.project extra76 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored194 stored195 rfl rfl
private theorem pc76w130 : PetersenPackedPin.project extra76 (0xffffffffffffffffffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc76w131 stored193 rfl rfl




private theorem pc76w139 : PetersenPackedPin.project extra76 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored194 stored199 rfl rfl
private theorem pc76w140 : PetersenPackedPin.project extra76 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored195 stored199 rfl rfl
private theorem pc76w138 : PetersenPackedPin.project extra76 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc76w139 pc76w140 rfl rfl

private theorem pc26w143 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w142 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w143 stored1 rfl rfl
private theorem pc26w145 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w144 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xffff0000ffff0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w38 pc26w145 rfl rfl
private theorem pc30w147 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w146 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc30w147 stored9 rfl rfl
private theorem pc30w149 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w148 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0xfa00fa00fa00fa00fa00fa00fa00fa00 := PetersenWireProjection.derive 3 pc30w85 pc30w149 rfl rfl
theorem b3_2898 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2898 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2898 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0xffff0000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w4 (PetersenWireProjection.cons pc0w1 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2899 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2899 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_2899 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w21 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons pc3w12 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2900 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2900 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2900 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w4 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2901 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2901 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2901 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w21 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w23 rfl)))))))))) (by decide +kernel)
theorem b3_2902 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2902 := by
  apply PetersenIndexedNode.close (bank := [s4_2253,a5438,a5439,a5440,a5441,a5442,a5443,s4_2849,a5444,a5445,a5446,a5447,a5448,a5449,a5450,a5451,a5452,a5453,s4_2686,a5454,a5455,a5456,a5457,a5458,a5459,s4_2873,a5460,a5461,s4_1407,a5462,a5463,a5464,s4_3143,a5465,s4_2676,s4_2600,a5466,a5467,a5468,a5469,a5470,s4_2892,a5471,a5472,a5473,a5474,s4_536,a5475,a5476,a5477,s4_3008,a5478,s4_2671,a5479,a5480,a5481,s4_2672]) (PetersenIndexedNode.reasons 256 17 420 0x622212021880884046444210118888c888422221010901084045030084044202840450602101140c0a0c0421221010420221013818084044202480830a098404e0606141281812020420221014808141012000840448402400120209080480821010a0808404280824200a0004808282014000a0205040280812021210048081888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050101404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301801b00c0406024808801a920220071003724051202006020301150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018018c00c2005e840480172101200690033801921012005a84048016400ac8404480880041080a004f0026801288406004821018015400a600502101801188406003f001e800e941020038504080114008600405040800d94102002f0016800a8a08200282820800d400660030282080098a082001f000e80068180a001806028009400460020060280058180a00150009212000c0600100301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b0120209212616024049202006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800200c0806050003800140006000f00068002c000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2253 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1324 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1321 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1316 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1411 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_3170 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2686 theta)
    · exact b4_2849 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_4 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_962 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_957 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2253 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1411 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1324 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1316 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1321 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3170 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2849 theta)
    · exact b4_2686 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2257 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1407 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1325 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1317 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1322 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3143 theta)
    · exact b4_2873 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2676 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2257 theta)
    · exact b4_1407 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1325 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1317 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1322 theta)
    · exact b4_3143 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2873 theta)
    · exact b4_2676 theta
    · exact b4_2600 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_536 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1346 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1339 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1342 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3008 theta)
    · exact b4_2892 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2671 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1336 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1335 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2600 theta)
    · exact b4_536 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1346 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1339 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1342 theta)
    · exact b4_3008 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2892 theta)
    · exact b4_2671 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_401 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1021 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2691 theta)
    · exact b4_2672 theta
theorem b3_2903 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2903 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2903 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffff0000,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w1 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w24 rfl)))))))))) (by decide +kernel)
theorem b3_2904 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2904 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2904 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w21 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w25 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2905 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2905 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_2905 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w27 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_2906 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2906 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2906 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w21 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w30 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2907 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2907 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s3_2907 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xff000000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w33 (PetersenWireProjection.cons pc0w32 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_2908 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2908 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s3_2908 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_2909 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2909 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,true),(4,true))] s3_2909 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xffffff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w9 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w33 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w44 rfl)))))))))) (by decide +kernel)
theorem b3_2910 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2910 := by
  apply PetersenIndexedNode.close (bank := [s4_2254,a5482,a5483,a5484,a5485,a5486,a5487,s4_2850,a5488,a5489,a5490,a5491,a5492,a5493,a5494,a5495,a5496,a5497,s4_2687,a5498,a5499,a5500,a5501,a5502,s4_3177,a5503,s4_2683,s4_2602,a5504,a5505,a5506,a5507,s4_3170,a5508,s4_2681,a5509,s4_1296,a5510,a5511,a5512,s4_3169,a5513,s4_2680,a5514,a5515,a5516,s4_540,a5517,a5518,a5519,a5520,a5521,s4_2678,a5522,s4_2679,s4_951,s4_2682]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404310110808c888420231111911084444202120210808901028202400108089080480024041210090104202141010808501048401400090105040280014040a08050102404242009010a030108088405080900374202280c200708424420208404420270301080884049010614130809c0c0c282503024040840442027060108088404a080311118809c1806222211128200840442028c0c1410230110808c8c04202230319180840c42020a08108084808141012000a02048402400120209080480828080a080a020988814100a080a08038301c10262207060283028200a0805040280824200a0004202282014000a020504028081080921004202840403012100120208480420021011090084044808018080c044c0c0301018089010c4c02404130318980480c2404018080c045444030101808a08016120b01151102c2406122820018080c042505030109404420226221080894144c44210510808180842022c2403010180850400e0a07010b0901c14060a1410018080c049212018080c05080883814180a484907029012420200c040603002c018080c049011000a2404400da006a480a494100c0406025040098884c052504131101889410006020301150500c04060221011312084045414262414050840406020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018018c00c2005e840480172101200690033801921012005a84048016400ac8404480880041080a004f0026801294102004850408015400a600505040801194102003f001e800e884060038210180114008600402101800d88406002f0016800a8a08200282820800d400660030282080098a082001f000e80068180a001806028009400460020060280058180a00150009212000c0600100301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030228a080c0806045040098904c08a282131201891410006040302108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800200c0806050003800140006000f00068002c000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2254 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1327 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1326 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1318 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1412 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3179 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2688 theta)
    · exact b4_2850 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_9 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_986 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_985 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2255 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1410 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1331 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1320 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1330 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3177 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2851 theta)
    · exact b4_2687 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2256 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1409 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1329 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1319 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1328 theta)
    · exact b4_3177 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2852 theta)
    · exact b4_2683 theta
    · exact b4_2602 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_542 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1348 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1340 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1347 theta)
    · exact b4_3170 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3131 theta)
    · exact b4_2681 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2652 theta)
    · exact b4_1296 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1357 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1355 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1356 theta)
    · exact b4_3169 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3132 theta)
    · exact b4_2680 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_997 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_996 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2605 theta)
    · exact b4_540 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1350 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1341 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1349 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3143 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3133 theta)
    · exact b4_2678 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2689 theta)
    · exact b4_2679 theta
    · exact b4_951 theta
    · exact b4_2682 theta
theorem b3_2911 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2911 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2911 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2912 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2912 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_2912 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w23 rfl)))))))))) (by decide +kernel)
theorem b3_2913 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2913 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2913 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w57 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w49 (PetersenWireProjection.cons stored113 rfl)))))))))) (by decide +kernel)
theorem b3_2914 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2914 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2914 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w62 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2915 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2915 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2915 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2916 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2916 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2916 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w65 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2917 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2917 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2917 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2918 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2918 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_2918 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2919 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2919 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_2919 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons pc1w74 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b3_2920 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2920 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2920 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w78 rfl))))))))) (by decide +kernel)
theorem b3_2921 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2921 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2921 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2922 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2922 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2922 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w64 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2923 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2923 := by
  apply PetersenIndexedNode.close (bank := [s4_2259,a5523,a5524,s4_2853,s4_2693,a4516,a5525,s4_2799,a5526,a5527,a5528,a5529,a5530,a5531,a5532,a5533,a5534,s4_1413,a5535,a5536,s4_2609,a5537,a5538,a5539,a5540,s4_2891,s4_2705,a5541,a4076,a5542,a4564,a4782,s4_1022,a5543,a5544,a5545,a4565,s4_2704,a5546,s4_2706,a5547,a5548,a5549,a5550,a5551,s4_2703]) (PetersenIndexedNode.reasons 256 17 432 0x622212021880884046444210118888c888422221010901084048016400ad40008404504028002005aa08050402101200548404311128200c4444808706012020c444e0c0211112021410048084808141012000840448402400120209080480821010a0808404280824200a0004808282014000a020504028081202121004808801414100a080a08038301c18200527060383028200a080504046060a081180884046460210111818c8c04206210105040840424040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406022606018080c0448086260120209818c4c02406120200c0406028013018080c04a08013110988a004e26221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301311100c0406024808313012020c444626024051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018011c008a00428404801021012004b0024501021012003e840431114007484044808800e10808c445001e31111202200364808800bc00584202a080800a8840600350019800c282020028a080383040048e0c05040800894100e0c1001338301410200205040141040038504048408006921005041000f141012102001848401311400284c4406028004818084c45000b13110180a001006021312400184c480301800280c044c490007131200c0600080301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800100c08060500011090084820006212010904000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2259 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1314 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1538 theta)
    · exact b4_2853 theta
    · exact b4_2693 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_97 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_528 theta)
    · exact b4_2799 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2308 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1413 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1312 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2862 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2259 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1538 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1314 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2853 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2308 theta)
    · exact b4_1413 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1312 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2862 theta)
    · exact b4_2609 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_533 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1333 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1332 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2968 theta)
    · exact b4_2891 theta
    · exact b4_2705 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2693 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_97 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_528 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2799 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2599 theta)
    · exact b4_1022 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1345 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1338 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1343 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2917 theta)
    · exact b4_2704 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1488 theta)
    · exact b4_2706 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1488 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2706 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2667 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_952 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_953 theta)
    · exact b4_2703 theta
theorem b3_2924 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2924 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false))] s3_2924 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xf000f000f000f000f000f000f000f000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w88 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w84 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_2925 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2925 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,false))] s3_2925 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons pc32w100 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w95 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_2926 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2926 := by
  intro m le c
  apply rejects_sound extra111 i5 4 tgt small111 hot111 [] s3_2926 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons stored184 (PetersenWireProjection.cons pc111w113 (PetersenWireProjection.cons stored183 (PetersenWireProjection.cons stored182 (PetersenWireProjection.cons stored181 (PetersenWireProjection.cons stored180 (PetersenWireProjection.cons stored179 (PetersenWireProjection.cons stored178 (PetersenWireProjection.cons pc111w104 (PetersenWireProjection.cons stored177 rfl)))))))))) (by decide +kernel)
theorem b3_2927 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2927 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2927 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2928 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2928 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s3_2928 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w122 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons pc74w120 (PetersenWireProjection.cons stored113 rfl)))))))))) (by decide +kernel)
theorem b3_2929 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2929 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2929 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w124 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_2930 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2930 := by
  apply PetersenIndexedNode.close (bank := [s4_2261,a5552,a5553,a5554,a5555,a5556,a5557,s4_2854,a5444,a5558,a5559,a5560,a5561,a5562,a5563,a5564,a5565,a5566,s4_2720,a5567,a5568,a5569,a5570,a5571,a5572,s4_2874,a5573,a5574,s4_1427,a5575,a5576,a5577,s4_3147,a5578,s4_2719,a5579,a5466,a5580,a5581,a5582,a5470,s4_2892,a5583,a5584,a5585,a5586,s4_536,a5587,a5588,a5589,s4_3008,a5478,s4_2717,s4_2722,s4_2718]) (PetersenIndexedNode.reasons 256 17 417 0xc4442404310110808c888420231111911084444202120210808a0601080884050808a0c042022818141808424420208404420270301080884049010614130809c0c0c28250302404084044202901028202400108089080480024041210090104202141010808501048401400090105040280014040a08050102404242009010311128200c4044202706010808c444e0c0211110809410042028c0c1410230110808c8c04202230319180840c42020a08108084808141012000a02048402400120209080480828080a080a020280824200a0004202282014000a020504028081080921004202988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018089010c4c02404130318980480c2404018080c042505030109404420226221080894144c44210510808180842025444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c049212018080c05080883814180a484907029012420200c040603002c018080c049011000a2404400da006a480a150500c04060221011312084045414262414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018018c00c2005e840480172101200690033801921012005a84048016400ac8404480880041080a004f0026801288406004821018015400a600502101801188406003f001e800e941020038504080114008600405040800d94102002f0016800a8a08200282820800d400660030282080098a082001f000e80068180a001806028009400460020060280058180a00150009212000c0600100301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b0120209212616024049202006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800200c0806050003800140006000f00068002c000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2261 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1310 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1309 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1308 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1575 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_3171 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2720 theta)
    · exact b4_2854 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_4 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_404 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_402 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2261 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1575 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1310 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1308 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1309 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3171 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2854 theta)
    · exact b4_2720 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2343 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1427 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1307 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1305 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1306 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3147 theta)
    · exact b4_2874 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2719 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2343 theta)
    · exact b4_1427 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1307 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1305 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1306 theta)
    · exact b4_3147 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2874 theta)
    · exact b4_2719 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2611 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_536 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1195 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1193 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1194 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3008 theta)
    · exact b4_2892 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2717 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1027 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1026 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2611 theta)
    · exact b4_536 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1195 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1193 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1194 theta)
    · exact b4_3008 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2892 theta)
    · exact b4_2717 theta
    · exact b4_2722 theta
    · exact b4_2718 theta
theorem b3_2931 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2931 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2931 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w126 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2932 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2932 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2932 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w13 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2933 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2933 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2933 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w128 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2934 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2934 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_2934 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2935 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2935 := by
  intro m le c
  apply rejects_sound extra76 i5 4 tgt small76 hot76 [] s3_2935 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000,0x0,0x0,0x0,0xcccccccc,0xff00ff00,0xaaaaaaaa,0xf0f0f0f0,0x0,0x0] (PetersenWireProjection.cons stored200 (PetersenWireProjection.cons pc76w138 (PetersenWireProjection.cons stored199 (PetersenWireProjection.cons stored198 (PetersenWireProjection.cons stored197 (PetersenWireProjection.cons stored196 (PetersenWireProjection.cons stored195 (PetersenWireProjection.cons stored194 (PetersenWireProjection.cons pc76w130 (PetersenWireProjection.cons stored193 rfl)))))))))) (by decide +kernel)
theorem b3_2936 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2936 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2936 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w66 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2937 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2937 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false))] s3_2937 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w144 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w142 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2938 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2938 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s3_2938 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w127 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w12 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_2939 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2939 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(0,true)),(false,(0,true),(4,false))] s3_2939 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xfa00fa00fa00fa00fa00fa00fa00fa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w148 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w146 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
