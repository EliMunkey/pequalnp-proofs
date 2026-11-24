import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L5S0
import Q1020K12L5S1
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc30w2 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl

private theorem pc30w1 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffff0f0f0f0fffffffffffffffffffffffff0f0f0f0 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc30w2 stored9 rfl rfl

private theorem pc30w8 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl

private theorem pc30w7 : PetersenPackedPin.project extra30 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w8 stored11 rfl rfl
private theorem pc30w11 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w6 : PetersenPackedPin.project extra30 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xfffffffffffffffffa00fa00fa00fa00 := PetersenWireProjection.derive 3 pc30w7 pc30w11 rfl rfl





private theorem pc32w16 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl

private theorem pc32w15 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w16 stored25 rfl rfl

private theorem pc32w22 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored26 stored29 rfl rfl

private theorem pc32w21 : PetersenPackedPin.project extra32 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffaaffaaffaaffaaff00ff00ff00ff00 := PetersenWireProjection.derive 3 pc32w22 stored27 rfl rfl
private theorem pc32w25 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl
private theorem pc32w20 : PetersenPackedPin.project extra32 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffaaffaaffaaffaaffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc32w21 pc32w25 rfl rfl





private theorem pc34w30 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored18 stored19 rfl rfl

private theorem pc34w29 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc34w30 stored17 rfl rfl

private theorem pc34w36 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w35 : PetersenPackedPin.project extra34 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w36 stored19 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w34 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0 := PetersenWireProjection.derive 3 pc34w35 pc34w38 rfl rfl





private theorem pc74w43 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl

private theorem pc74w42 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w43 stored113 rfl rfl

private theorem pc74w49 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl

private theorem pc74w48 : PetersenPackedPin.project extra74 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc74w49 stored116 rfl rfl
private theorem pc74w52 : PetersenPackedPin.project extra74 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored114 stored119 rfl rfl
private theorem pc74w47 : PetersenPackedPin.project extra74 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc74w48 pc74w52 rfl rfl






private theorem pc26w57 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl

private theorem pc26w60 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl

private theorem pc26w64 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl

private theorem pc26w63 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w64 stored3 rfl rfl
private theorem pc26w67 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w62 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffffccccffffcccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w63 pc26w67 rfl rfl


private theorem pc32w70 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl
private theorem pc32w71 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc74w72 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl



private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl

private theorem pc3w77 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w81 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl

private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w81 stored36 rfl rfl
private theorem pc3w83 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w80 pc3w83 rfl rfl






private theorem pc108w88 : PetersenPackedPin.project extra108 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored313 stored314 rfl rfl

private theorem pc108w92 : PetersenPackedPin.project extra108 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored313 stored315 rfl rfl

private theorem pc108w94 : PetersenPackedPin.project extra108 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored314 stored316 rfl rfl
private theorem pc108w91 : PetersenPackedPin.project extra108 (0xffffffffffffccccffffffffffff0000ffffffffffffccccffffffffffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w92 pc108w94 rfl rfl
private theorem pc108w98 : PetersenPackedPin.project extra108 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored314 stored315 rfl rfl
private theorem pc108w97 : PetersenPackedPin.project extra108 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w98 stored316 rfl rfl
private theorem pc108w96 : PetersenPackedPin.project extra108 (0xffffccccffffccccffffccccffff0000ffffccccffffccccffffccccffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w97 pc108w92 rfl rfl



private theorem pc34w103 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w102 : PetersenPackedPin.project extra34 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0fafafafafafafafa := PetersenWireProjection.derive 3 pc34w103 pc34w30 rfl rfl
private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl
private theorem pc34w105 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w103 pc34w106 rfl rfl
private theorem pc34w107 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffccccffff0000ffffffffffffffffffffccccffff0000 : BitVec 256) = 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0 := PetersenWireProjection.derive 3 pc34w106 pc34w36 rfl rfl
private theorem pc30w109 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored9 stored10 rfl rfl
private theorem pc30w110 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc30w108 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffffffffffff0f0fffff0f0fffff0f0fffffffffffff0f0 : BitVec 256) = 0xffffffffffffffff0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 3 pc30w109 pc30w110 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored11 stored14 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xffffccccffffccccffffffffffffccccffffccccffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc30w109 pc30w112 rfl rfl



private theorem pc35w115 : PetersenPackedPin.project extra35 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored219 stored224 rfl rfl

private theorem pc35w114 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w115 stored218 rfl rfl
private theorem pc35w120 : PetersenPackedPin.project extra35 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 2 stored218 stored219 rfl rfl

private theorem pc35w121 : PetersenPackedPin.project extra35 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored224 stored222 rfl rfl
private theorem pc35w119 : PetersenPackedPin.project extra35 (0xffffccccffffccccffffffffffffccccffffccccffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w120 pc35w121 rfl rfl



private theorem pc30w126 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffff00ff00 := PetersenWireProjection.derive 3 pc30w112 stored8 rfl rfl
private theorem pc30w128 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w127 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffffcfcfffffcfcfffffcfcfffffcfc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w128 pc30w110 rfl rfl
private theorem pc30w130 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored8 stored11 rfl rfl
private theorem pc30w129 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffff0a0a0a0a := PetersenWireProjection.derive 3 pc30w130 pc30w109 rfl rfl
private theorem pc30w131 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffffaa00aa00 := PetersenWireProjection.derive 3 pc30w130 pc30w8 rfl rfl
private theorem pc30w132 : PetersenPackedPin.project extra30 (0xfffffcfcfffff0f0fffffcfcfffff0f0fffffcfcfffff0f0fffffcfcfffff0f0 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w8 pc30w110 rfl rfl



private theorem pc69w137 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored100 rfl rfl

private theorem pc69w136 : PetersenPackedPin.project extra69 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc69w137 stored101 rfl rfl

private theorem pc69w140 : PetersenPackedPin.project extra69 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored97 stored99 rfl rfl
private theorem pc69w135 : PetersenPackedPin.project extra69 (0xffffffffffffccccffffffffffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc69w136 pc69w140 rfl rfl
private theorem pc69w142 : PetersenPackedPin.project extra69 (0xffffffffccccccccffffffff00000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w140 pc69w137 rfl rfl





private theorem pc1w146 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl


private theorem pc1w149 : PetersenPackedPin.project cycle1 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored58 stored63 rfl rfl

private theorem pc1w153 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl
private theorem pc1w155 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w152 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w153 pc1w155 rfl rfl





private theorem pc41w159 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl

private theorem pc41w162 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl


private theorem pc41w167 : PetersenPackedPin.project extra41 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffccccccccffffffffcccccccc := PetersenWireProjection.derive 3 stored92 stored95 rfl rfl
private theorem pc41w166 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w167 stored91 rfl rfl
private theorem pc41w169 : PetersenPackedPin.project extra41 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 3 stored90 stored92 rfl rfl
private theorem pc41w165 : PetersenPackedPin.project extra41 (0xffffffffffff0000ffffffffffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffffffffff00000000 := PetersenWireProjection.derive 0 pc41w166 pc41w169 rfl rfl



theorem b4_3150 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3150 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(0,true)),(false,(0,true),(4,false)),(false,(0,true),(8,true))] s4_3150 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffffa00fa00fa00fa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w6 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w1 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_3151 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3151 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false)),(false,(0,true),(5,true))] s4_3151 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaffaaffaaffaaffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w20 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w15 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3152 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3152 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true)),(false,(0,true),(1,false))] s4_3152 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w34 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w29 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_3153 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3153 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3153 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w47 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w42 rfl))))))))) (by decide +kernel)
theorem b4_3154 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3154 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(0,true),(5,false)),(false,(0,true),(3,true))] s4_3154 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w60 (PetersenWireProjection.cons pc26w57 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3155 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3155 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false)),(false,(0,true),(5,true))] s4_3155 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaffaaffaaffaaffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w20 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w71 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3156 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3156 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3156 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w47 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w43 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w72 rfl))))))))) (by decide +kernel)
theorem b4_3157 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3157 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true))] s4_3157 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w79 (PetersenWireProjection.cons pc3w77 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3158 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3158 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(6,true)),(false,(0,true),(1,false)),(false,(0,true),(5,true))] s4_3158 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaffaaffaaffaaffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w20 (PetersenWireProjection.cons pc32w16 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w70 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3159 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3159 := by
  intro m le c
  apply rejects_sound extra108 i6 5 tgt small108 hot108 [] s4_3159 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffffffffffff,0xffffffffffffffff,0x0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored319 (PetersenWireProjection.cons stored315 (PetersenWireProjection.cons stored318 (PetersenWireProjection.cons stored317 (PetersenWireProjection.cons pc108w96 (PetersenWireProjection.cons pc108w91 (PetersenWireProjection.cons stored313 (PetersenWireProjection.cons pc108w88 (PetersenWireProjection.cons stored312 rfl))))))))) (by decide +kernel)
theorem b4_3160 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3160 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(0,true),(3,true))] s4_3160 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0fafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_3161 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3161 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(0,true),(5,true))] s4_3161 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w105 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_3162 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3162 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false)),(false,(0,true),(5,true))] s4_3162 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w107 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b4_3163 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3163 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(7,true)),(false,(0,false),(5,true))] s4_3163 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffff0aff0aff0aff0a,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b4_3164 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3164 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3164 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w119 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons pc35w114 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3165 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3165 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true)),(false,(0,false),(7,true))] s4_3165 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffff00ff00] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w127 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w126 rfl))))))))) (by decide +kernel)
theorem b4_3166 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3166 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,true)),(false,(0,true),(7,true)),(false,(0,false),(7,true))] s4_3166 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffff0a0a0a0a] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w108 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w129 rfl))))))))) (by decide +kernel)
theorem b4_3167 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3167 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(3,false)),(false,(0,true),(7,true)),(false,(0,false),(7,true))] s4_3167 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffaa00aa00] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w132 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w131 rfl))))))))) (by decide +kernel)
theorem b4_3168 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3168 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_3168 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00,0xffff0000,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons pc69w142 (PetersenWireProjection.cons pc69w135 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_3169 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3169 := by
  apply node_sound (nxt := [a6627,a6628,s5_10,s5_44])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_10 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_44 theta)
    · exact b5_10 theta
    · exact b5_44 theta
theorem b4_3170 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3170 := by
  apply node_sound (nxt := [s5_15,s5_40])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_15 theta
    · exact b5_40 theta
theorem b4_3171 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3171 := by
  apply node_sound (nxt := [s5_16,s5_43])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_16 theta
    · exact b5_43 theta
theorem b4_3172 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3172 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [(false,(2,true),(1,true))] s4_3172 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f0f0f0,0xfcfcfcfc,0x0,0xffff0000] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w152 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w149 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w146 rfl))))))))) (by decide +kernel)
theorem b4_3173 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3173 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [(false,(6,true),(5,true))] s4_3173 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffff00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons pc41w165 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w162 (PetersenWireProjection.cons pc41w159 rfl))))))))) (by decide +kernel)
theorem b4_3174 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3174 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3175 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3175 := by
  apply node_sound (nxt := [a6629,a6630])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b5_12 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_48 theta)
theorem b4_3176 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3176 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3177 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3177 := by
  apply node_sound (nxt := [a6631,a6632,s5_11,s5_45])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) (b5_13 theta)
    · exact via sym3 fix3 (by decide +kernel) (b5_49 theta)
    · exact b5_11 theta
    · exact b5_45 theta
theorem b4_3178 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3178 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3179 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3179 := by
  apply node_sound (nxt := [a6633,a6634,a6635,s5_50])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b5_14 theta)
    · exact via sym1 fix1 (by decide +kernel) (b5_50 theta)
    · exact via sym6 fix6 (by decide +kernel) (b5_14 theta)
    · exact b5_50 theta
theorem b4_3180 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3180 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3181 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3181 := by
  apply node_sound (nxt := [s5_38,a6636,a6637,s5_52,a6638,a6639,a6640,a6641,a6642,a6643,a6644,a6645,s5_26,a6646,a6647,s5_34,a6648,s5_51,s5_0,a6649,a6650,a6651,a6652,a6653])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b5_38 theta
    · exact via sym6 fix6 (by decide +kernel) (b5_34 theta)
    · exact via sym6 fix6 (by decide +kernel) (b5_26 theta)
    · exact b5_52 theta
    · exact via sym4 fix4 (by decide +kernel) (b5_26 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_52 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_38 theta)
    · exact via sym4 fix4 (by decide +kernel) (b5_34 theta)
    · exact via sym4 fix4 (by decide +kernel) (b5_38 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_34 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_26 theta)
    · exact via sym4 fix4 (by decide +kernel) (b5_52 theta)
    · exact b5_26 theta
    · exact via sym6 fix6 (by decide +kernel) (b5_52 theta)
    · exact via sym6 fix6 (by decide +kernel) (b5_38 theta)
    · exact b5_34 theta
    · exact via sym6 fix6 (by decide +kernel) (b5_51 theta)
    · exact b5_51 theta
    · exact b5_0 theta
    · exact via sym6 fix6 (by decide +kernel) (b5_0 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_51 theta)
    · exact via sym4 fix4 (by decide +kernel) (b5_51 theta)
    · exact via sym4 fix4 (by decide +kernel) (b5_0 theta)
    · exact via sym2 fix2 (by decide +kernel) (b5_0 theta)
end Orbits1020Cost12
