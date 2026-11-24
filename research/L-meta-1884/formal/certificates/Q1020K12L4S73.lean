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



private theorem pc32w2 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl

private theorem pc32w1 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffff00ff00ffffffffffffffffffffffffff00ff00 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc32w2 stored25 rfl rfl

private theorem pc32w7 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl

private theorem pc32w6 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w7 stored27 rfl rfl





private theorem pc35w15 : PetersenPackedPin.project extra35 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored219 stored224 rfl rfl

private theorem pc35w14 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w15 stored218 rfl rfl

private theorem pc35w19 : PetersenPackedPin.project extra35 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored217 stored222 rfl rfl
private theorem pc35w13 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w14 pc35w19 rfl rfl
private theorem pc35w21 : PetersenPackedPin.project extra35 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w19 stored224 rfl rfl





private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl


private theorem pc26w29 : PetersenPackedPin.project extra26 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffccccffffccccffffccccffffcccc := PetersenWireProjection.derive 3 stored3 stored6 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffeeeeffffeeeeffffeeeeffffeeee : BitVec 256) = 0xfffffcfcfffffcfcfffffcfcfffffcfc := PetersenWireProjection.derive 3 pc26w26 pc26w29 rfl rfl


private theorem pc26w35 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w35 stored3 rfl rfl




private theorem pc30w39 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl


private theorem pc30w42 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc30w38 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffcfcfffffcfcfffffcfcfffffcfc : BitVec 256) = 0xffffffffffffffffffffffffff00ff00 := PetersenWireProjection.derive 3 pc30w39 pc30w42 rfl rfl


private theorem pc30w48 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w47 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w48 stored11 rfl rfl


private theorem pc32w52 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored24 stored29 rfl rfl
private theorem pc32w53 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl
private theorem pc32w51 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffccffffffccffffffccffffffcc : BitVec 256) = 0xfffafffafffafffafffafffafffafffa := PetersenWireProjection.derive 3 pc32w52 pc32w53 rfl rfl


private theorem pc41w55 : PetersenPackedPin.project extra41 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored89 stored90 rfl rfl

private theorem pc41w54 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w55 stored91 rfl rfl

private theorem pc41w60 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored95 rfl rfl

private theorem pc41w59 : PetersenPackedPin.project extra41 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 3 pc41w60 stored92 rfl rfl





private theorem pc1w66 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl


private theorem pc1w71 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl

private theorem pc1w70 : PetersenPackedPin.project cycle1 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w71 stored60 rfl rfl



private theorem pc26w78 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w78 stored0 rfl rfl


private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl

private theorem pc3w79 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w80 stored33 rfl rfl

private theorem pc3w86 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w85 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w86 stored36 rfl rfl



private theorem pc30w92 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl
private theorem pc30w91 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 pc30w92 stored8 rfl rfl
private theorem pc32w93 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w2 stored24 rfl rfl
private theorem pc35w95 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored217 stored222 rfl rfl
private theorem pc35w94 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w95 pc35w15 rfl rfl
private theorem pc1w96 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl
private theorem pc26w98 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w97 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w98 stored0 rfl rfl
private theorem pc3w100 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w99 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w100 stored33 rfl rfl
private theorem pc30w102 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl
private theorem pc30w101 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w102 stored8 rfl rfl
private theorem pc32w104 : PetersenPackedPin.project extra32 (0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored28 rfl rfl
private theorem pc32w103 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc32w104 stored24 rfl rfl
private theorem pc35w106 : PetersenPackedPin.project extra35 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored218 stored224 rfl rfl
private theorem pc35w105 : PetersenPackedPin.project extra35 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc35w95 pc35w106 rfl rfl
private theorem pc41w108 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored89 stored90 rfl rfl
private theorem pc41w107 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w108 stored91 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 stored33 stored34 rfl rfl
private theorem pc3w111 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc32w112 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc32w113 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc32w114 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl
private theorem pc41w115 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
private theorem pc41w117 : PetersenPackedPin.project extra41 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffccccccccffffffffcccccccc := PetersenWireProjection.derive 3 stored92 stored95 rfl rfl
private theorem pc41w116 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w117 stored91 rfl rfl
private theorem pc26w118 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc30w119 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl
private theorem pc32w120 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored25 stored26 rfl rfl


private theorem pc74w121 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl

private theorem pc74w125 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored113 stored119 rfl rfl

private theorem pc74w127 : PetersenPackedPin.project extra74 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored116 rfl rfl
private theorem pc74w124 : PetersenPackedPin.project extra74 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffffccccffffcccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc74w125 pc74w127 rfl rfl

private theorem pc74w130 : PetersenPackedPin.project extra74 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc74w125 stored116 rfl rfl



private theorem pc74w134 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl
private theorem pc3w135 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl
private theorem pc30w136 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffaaaaaaaaffffffffaaaaaaaa := PetersenWireProjection.derive 3 stored8 stored10 rfl rfl



private theorem pc108w138 : PetersenPackedPin.project extra108 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored313 stored314 rfl rfl

private theorem pc108w142 : PetersenPackedPin.project extra108 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored312 stored315 rfl rfl

private theorem pc108w144 : PetersenPackedPin.project extra108 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored314 stored316 rfl rfl
private theorem pc108w141 : PetersenPackedPin.project extra108 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w142 pc108w144 rfl rfl
private theorem pc108w146 : PetersenPackedPin.project extra108 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc108w142 stored316 rfl rfl





private theorem pc109w150 : PetersenPackedPin.project extra109 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored225 stored227 rfl rfl


private theorem pc109w155 : PetersenPackedPin.project extra109 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored225 stored228 rfl rfl

private theorem pc109w157 : PetersenPackedPin.project extra109 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 stored227 stored229 rfl rfl
private theorem pc109w154 : PetersenPackedPin.project extra109 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 pc109w155 pc109w157 rfl rfl
private theorem pc109w159 : PetersenPackedPin.project extra109 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc109w155 stored229 rfl rfl



private theorem pc26w164 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w163 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffffccccffffffffffffcccc : BitVec 256) = 0xffffffffffffffffcfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w35 pc26w164 rfl rfl
private theorem pc26w166 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl
private theorem pc26w165 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffeeeeffffeeeeffffeeeeffffeeee : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w35 pc26w166 rfl rfl




private theorem pc16w171 : PetersenPackedPin.project tree16 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored147 stored148 rfl rfl

private theorem pc16w170 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc16w171 stored149 rfl rfl
private theorem pc16w175 : PetersenPackedPin.project tree16 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored145 stored146 rfl rfl
private theorem pc16w174 : PetersenPackedPin.project tree16 (0xffffccccffff0000ffffccccffff0000ffffccccffff00000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc16w170 pc16w175 rfl rfl



theorem b4_3066 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3066 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true)),(false,(1,true),(5,true))] s4_3066 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w1 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3067 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3067 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3067 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w21 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons pc35w13 (PetersenWireProjection.cons stored217 rfl))))))))) (by decide +kernel)
theorem b4_3068 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3068 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true)),(false,(0,false),(4,true))] s4_3068 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffcfcfffffcfcfffffcfcfffffcfc] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w25 rfl))))))))) (by decide +kernel)
theorem b4_3069 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3069 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true)),(false,(0,false),(7,true))] s4_3069 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffff00ff00] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w47 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w38 rfl))))))))) (by decide +kernel)
theorem b4_3070 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3070 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(0,true),(4,true)),(false,(0,false),(4,true))] s4_3070 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffafffafffafffafffafffafffafffa] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w51 rfl))))))))) (by decide +kernel)
theorem b4_3071 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3071 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_3071 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons pc41w59 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w54 rfl))))))))) (by decide +kernel)
theorem b4_3072 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3072 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_3072 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0x0,0xffff0000] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w70 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w66 rfl))))))))) (by decide +kernel)
theorem b4_3073 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3073 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(3,true)),(false,(1,true),(3,true))] s4_3073 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w77 rfl))))))))) (by decide +kernel)
theorem b4_3074 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3074 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s4_3074 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w79 rfl))))))))) (by decide +kernel)
theorem b4_3075 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3075 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(6,true)),(false,(1,true),(8,true))] s4_3075 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w47 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w91 rfl))))))))) (by decide +kernel)
theorem b4_3076 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3076 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(3,true)),(false,(1,true),(5,true))] s4_3076 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w93 rfl))))))))) (by decide +kernel)
theorem b4_3077 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3077 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3077 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w21 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 (PetersenWireProjection.cons pc35w94 rfl))))))))) (by decide +kernel)
theorem b4_3078 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3078 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s4_3078 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0x0,0xf0f0f0f0] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w70 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w96 rfl))))))))) (by decide +kernel)
theorem b4_3079 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3079 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(1,true),(3,true)),(false,(1,true),(3,true))] s4_3079 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w97 rfl))))))))) (by decide +kernel)
theorem b4_3080 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3080 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3080 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w99 rfl))))))))) (by decide +kernel)
theorem b4_3081 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3081 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(3,true),(6,true)),(false,(1,true),(8,true))] s4_3081 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w47 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w101 rfl))))))))) (by decide +kernel)
theorem b4_3082 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3082 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(5,true),(3,true)),(false,(1,true),(5,true))] s4_3082 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w103 rfl))))))))) (by decide +kernel)
theorem b4_3083 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3083 := by
  intro m le c
  apply rejects_sound extra35 i7 6 tgt small35 hot35 [] s4_3083 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored223 (PetersenWireProjection.cons stored222 (PetersenWireProjection.cons stored221 (PetersenWireProjection.cons stored220 (PetersenWireProjection.cons pc35w21 (PetersenWireProjection.cons stored219 (PetersenWireProjection.cons stored218 (PetersenWireProjection.cons stored217 (PetersenWireProjection.cons pc35w105 rfl))))))))) (by decide +kernel)
theorem b4_3084 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3084 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_3084 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons pc41w59 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w107 rfl))))))))) (by decide +kernel)
theorem b4_3085 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3085 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(3,true)),(false,(1,true),(3,true))] s4_3085 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons pc26w109 rfl))))))))) (by decide +kernel)
theorem b4_3086 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3086 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s4_3086 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfffff0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w111 (PetersenWireProjection.cons pc3w110 rfl))))))))) (by decide +kernel)
theorem b4_3087 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3087 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(3,true)),(false,(1,true),(5,true))] s4_3087 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w113 (PetersenWireProjection.cons pc32w112 rfl))))))))) (by decide +kernel)
theorem b4_3088 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3088 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(5,true),(3,true)),(false,(1,true),(5,true))] s4_3088 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w113 (PetersenWireProjection.cons pc32w114 rfl))))))))) (by decide +kernel)
theorem b4_3089 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3089 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s4_3089 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons pc41w59 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w116 (PetersenWireProjection.cons pc41w115 rfl))))))))) (by decide +kernel)
theorem b4_3090 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3090 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3091 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3091 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(1,true)),(false,(1,true),(3,true))] s4_3091 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w98 (PetersenWireProjection.cons pc26w118 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3092 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3092 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(3,true),(6,true)),(false,(1,true),(8,true))] s4_3092 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w47 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w102 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w119 rfl))))))))) (by decide +kernel)
theorem b4_3093 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3093 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true)),(false,(1,true),(5,true))] s4_3093 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w104 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3094 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3094 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3094 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w130 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w124 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w121 rfl))))))))) (by decide +kernel)
theorem b4_3095 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3095 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_3095 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons pc74w130 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w134 (PetersenWireProjection.cons stored113 (PetersenWireProjection.cons pc74w121 rfl))))))))) (by decide +kernel)
theorem b4_3096 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3096 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s4_3096 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w85 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w135 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_3097 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3097 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(1,true),(6,true)),(false,(1,true),(8,true))] s4_3097 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w47 (PetersenWireProjection.cons pc30w92 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w136 rfl))))))))) (by decide +kernel)
theorem b4_3098 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3098 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(7,true),(5,true)),(false,(1,true),(5,true))] s4_3098 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w6 (PetersenWireProjection.cons pc32w2 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b4_3099 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3099 := by
  intro m le c
  apply rejects_sound extra108 i6 5 tgt small108 hot108 [] s4_3099 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffffffffffff,0xffffffffffffffff,0x0,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored319 (PetersenWireProjection.cons stored315 (PetersenWireProjection.cons stored318 (PetersenWireProjection.cons stored317 (PetersenWireProjection.cons pc108w146 (PetersenWireProjection.cons pc108w141 (PetersenWireProjection.cons stored313 (PetersenWireProjection.cons pc108w138 (PetersenWireProjection.cons stored312 rfl))))))))) (by decide +kernel)
theorem b4_3100 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3100 := by
  intro m le c
  apply rejects_sound extra109 i6 5 tgt small109 hot109 [] s4_3100 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xffff0000ffff0000,0xff00ff00ff00ff00,0x0,0xffffffff00000000,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored232 (PetersenWireProjection.cons stored228 (PetersenWireProjection.cons stored231 (PetersenWireProjection.cons stored230 (PetersenWireProjection.cons pc109w159 (PetersenWireProjection.cons pc109w154 (PetersenWireProjection.cons stored226 (PetersenWireProjection.cons stored225 (PetersenWireProjection.cons pc109w150 rfl))))))))) (by decide +kernel)
theorem b4_3101 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3101 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3102 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3102 := by
  apply node_sound (nxt := [a6620,s5_39])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact via sym3 fix3 (by decide +kernel) (b5_21 theta)
    · exact b5_39 theta
theorem b4_3103 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3103 := by
  apply node_sound (nxt := [s5_6,a6621])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_6 theta
    · exact via sym3 fix3 (by decide +kernel) (b5_46 theta)
theorem b4_3104 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3104 := by
  apply node_sound (nxt := [s5_7,a6622])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact b5_7 theta
    · exact via sym3 fix3 (by decide +kernel) (b5_47 theta)
theorem b4_3105 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3105 := by
  apply node_sound (nxt := [])
  · decide +kernel
  · intro R mem
    simp at mem
theorem b4_3106 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3106 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true)),(false,(0,false),(8,true))] s4_3106 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffcfcfcccccfcfcccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w165 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w163 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_3107 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_3107 := by
  intro m le c
  apply rejects_sound tree16 i6 6 tgt small16 hot16 [] s4_3107 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0x0,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000] (PetersenWireProjection.cons stored152 (PetersenWireProjection.cons stored148 (PetersenWireProjection.cons stored151 (PetersenWireProjection.cons stored150 (PetersenWireProjection.cons pc16w174 (PetersenWireProjection.cons pc16w170 (PetersenWireProjection.cons stored147 (PetersenWireProjection.cons stored146 (PetersenWireProjection.cons stored145 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
