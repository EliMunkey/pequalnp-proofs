import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S58
import Q1020K12L4S59
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S67
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0







private theorem pc3w7 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w6 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w7 pc3w9 rfl rfl

private theorem pc3w12 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w12 stored33 rfl rfl
private theorem pc3w13 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored33 stored35 rfl rfl





private theorem pc32w20 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored24 stored28 rfl rfl
private theorem pc32w21 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored26 stored28 rfl rfl
private theorem pc32w19 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000ff00ff0000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc32w20 pc32w21 rfl rfl



private theorem pc32w26 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored26 stored29 rfl rfl
private theorem pc32w25 : PetersenPackedPin.project extra32 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w26 stored24 rfl rfl
private theorem pc32w27 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored26 rfl rfl
private theorem pc32w28 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff0033003300ff00ff0033003300 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc32w25 stored28 rfl rfl



private theorem pc2w32 : PetersenPackedPin.project cycle2 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored42 stored43 rfl rfl





private theorem pc2w39 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl
private theorem pc2w38 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 1 pc2w39 stored41 rfl rfl
private theorem pc2w40 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored41 stored43 rfl rfl
private theorem pc2w41 : PetersenPackedPin.project cycle2 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored41 stored43 rfl rfl
private theorem pc3w43 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w42 : PetersenPackedPin.project cycle3 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w43 stored35 rfl rfl
private theorem pc3w44 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w7 stored35 rfl rfl
private theorem pc3w45 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl



private theorem pc73w49 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 stored129 stored131 rfl rfl
private theorem pc73w48 : PetersenPackedPin.project extra73 (0xffffffffffffffff0000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w49 stored130 rfl rfl





private theorem pc73w57 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored131 stored135 rfl rfl
private theorem pc73w56 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w57 stored129 rfl rfl
private theorem pc3w58 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc3w59 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored34 stored35 rfl rfl


private theorem pc26w61 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl

private theorem pc26w60 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w61 stored0 rfl rfl





private theorem pc26w71 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc : BitVec 256) = 0xf0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w71 stored0 rfl rfl
private theorem pc3w72 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w45 stored33 rfl rfl
private theorem pc32w74 : PetersenPackedPin.project extra32 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored26 stored28 rfl rfl
private theorem pc32w73 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w74 stored24 rfl rfl


private theorem pc37w76 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored65 stored66 rfl rfl

private theorem pc37w75 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w76 stored67 rfl rfl





private theorem pc37w86 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored66 stored71 rfl rfl
private theorem pc37w85 : PetersenPackedPin.project extra37 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc37w86 stored67 rfl rfl
private theorem pc3w87 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w12 stored33 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc32w90 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc3w91 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w11 stored36 rfl rfl
private theorem pc3w93 : PetersenPackedPin.project cycle3 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored34 stored35 rfl rfl
private theorem pc3w92 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w43 pc3w93 rfl rfl



private theorem pc0w97 : PetersenPackedPin.project cycle0 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored51 rfl rfl





private theorem pc0w104 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w103 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 1 pc0w104 pc0w97 rfl rfl


private theorem pc41w106 : PetersenPackedPin.project extra41 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored89 stored90 rfl rfl

private theorem pc41w105 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w106 stored91 rfl rfl





private theorem pc41w116 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored95 rfl rfl
private theorem pc41w115 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w116 pc41w106 rfl rfl








private theorem pc30w126 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored8 stored13 rfl rfl
private theorem pc30w127 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w125 : PetersenPackedPin.project extra30 (0xf0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc30w126 pc30w127 rfl rfl
private theorem pc30w128 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xffffffffa0a0a0a0ffffffffa0a0a0a0 := PetersenWireProjection.derive 3 pc30w127 stored8 rfl rfl
private theorem pc32w130 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored24 stored28 rfl rfl
private theorem pc32w131 : PetersenPackedPin.project extra32 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored25 stored26 rfl rfl
private theorem pc32w129 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc32w130 pc32w131 rfl rfl
private theorem pc32w132 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc32w131 stored24 rfl rfl








private theorem pc34w142 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored16 stored19 rfl rfl
private theorem pc34w143 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl
private theorem pc34w141 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc34w142 pc34w143 rfl rfl
private theorem pc34w144 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xfffffffffffffffff0f00000f0f00000 := PetersenWireProjection.derive 3 pc34w143 stored16 rfl rfl
private theorem pc41w146 : PetersenPackedPin.project extra41 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored89 stored95 rfl rfl
private theorem pc41w145 : PetersenPackedPin.project extra41 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc41w146 stored91 rfl rfl
private theorem pc41w148 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl
private theorem pc41w147 : PetersenPackedPin.project extra41 (0xffffffff00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc41w148 pc41w146 rfl rfl
private theorem pc73w149 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w150 : PetersenPackedPin.project extra73 (0xffffffff00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc73w49 pc73w149 rfl rfl
private theorem pc37w151 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl
private theorem pc37w153 : PetersenPackedPin.project extra37 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored65 stored71 rfl rfl
private theorem pc37w152 : PetersenPackedPin.project extra37 (0xffffffff00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 pc37w151 pc37w153 rfl rfl
private theorem pc34w154 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w155 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w157 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w156 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc34w157 stored16 rfl rfl
private theorem pc34w158 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 2 stored16 stored18 rfl rfl
private theorem pc34w159 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored16 stored17 rfl rfl
private theorem pc34w160 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 2 stored17 stored18 rfl rfl
private theorem pc34w161 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 1 stored17 stored18 rfl rfl
theorem b3_252 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_252 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_252 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w6 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_253 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_253 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_253 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w6 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w13 rfl)))))))))) (by decide +kernel)
theorem b3_254 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_254 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_254 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w25 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w19 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_255 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_255 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_255 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w25 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons pc32w28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w27 rfl)))))))))) (by decide +kernel)
theorem b3_256 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_256 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_256 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w38 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w32 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))))) (by decide +kernel)
theorem b3_257 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_257 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [(false,(0,false),(2,true))] s3_257 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc2w38 (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons pc2w41 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w40 rfl)))))))))) (by decide +kernel)
theorem b3_258 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_258 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_258 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w42 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_259 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_259 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_259 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w44 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_260 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_260 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_260 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w45 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_261 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_261 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_261 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w56 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons pc73w48 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_262 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_262 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_262 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w58 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_263 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_263 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(4,true))] s3_263 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffffcccc,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w59 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_264 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_264 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_264 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_265 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_265 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_265 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w13 rfl)))))))))) (by decide +kernel)
theorem b3_266 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_266 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,false))] s3_266 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w60 rfl)))))))))) (by decide +kernel)
theorem b3_267 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_267 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_267 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w72 rfl)))))))))) (by decide +kernel)
theorem b3_268 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_268 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_268 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w25 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w73 rfl)))))))))) (by decide +kernel)
theorem b3_269 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_269 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_269 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc37w85 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w75 rfl)))))))))) (by decide +kernel)
theorem b3_270 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_270 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_270 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w87 rfl))))))))) (by decide +kernel)
theorem b3_271 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_271 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s3_271 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w87 (PetersenWireProjection.cons pc3w13 rfl)))))))))) (by decide +kernel)
theorem b3_272 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_272 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true)),(false,(5,false),(0,false))] s3_272 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons pc26w88 rfl)))))))))) (by decide +kernel)
theorem b3_273 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_273 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(2,true)),(false,(1,false),(0,false))] s3_273 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w25 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w90 (PetersenWireProjection.cons pc32w27 rfl)))))))))) (by decide +kernel)
theorem b3_274 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_274 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s3_274 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons pc3w11 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w91 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w13 rfl)))))))))) (by decide +kernel)
theorem b3_275 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_275 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_275 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons pc3w43 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_276 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_276 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s3_276 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcc00cc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons pc0w103 (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons pc0w97 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl)))))))))) (by decide +kernel)
theorem b3_277 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_277 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_277 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w92 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_278 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_278 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_278 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w115 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w105 rfl)))))))))) (by decide +kernel)
theorem b3_279 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_279 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [] s3_279 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w125 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_280 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_280 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,false),(2,false)),(false,(0,true),(6,true))] s3_280 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xffffffffa0a0a0a0ffffffffa0a0a0a0] (PetersenWireProjection.cons pc30w125 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w128 rfl)))))))))) (by decide +kernel)
theorem b3_281 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_281 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [] s3_281 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w129 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_282 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_282 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,false),(4,false)),(false,(0,true),(3,true))] s3_282 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w129 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w132 rfl)))))))))) (by decide +kernel)
theorem b3_283 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_283 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [] s3_283 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w141 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_284 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_284 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(2,false),(4,false)),(false,(0,true),(7,true))] s3_284 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f00000f0f00000] (PetersenWireProjection.cons pc34w141 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w144 rfl)))))))))) (by decide +kernel)
theorem b3_285 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_285 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_285 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w147 (PetersenWireProjection.cons pc41w145 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 rfl)))))))))) (by decide +kernel)
theorem b3_286 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_286 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_286 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w150 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons pc73w149 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_287 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_287 := by
  apply PetersenIndexedNode.close (bank := [s4_173,a4091,a4092,s4_2487,s4_204,a4093,s4_2771,s4_2794,a4094,a4095,a4096,a4097,a4098,a4099,a4100,a4101,a4102,s4_163,a4103,a4104,s4_3,a4105,a4106,a4107,s4_19,a4108,a4109,a4110,s4_223]) (PetersenIndexedNode.reasons 256 17 420 0x70301080884048404614121011c0c0c28250302101084044202501008405400084045040280014040a0805010210104202210131110840442024202706018404c444e0c0311110808420221014808141012000840448402400120209080480821010a0808404290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210146060a081180884046460210111818c8c04206210105040840425050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e081311038301418141005040282042020180908009010424021001080884804202240400c0406023a1a018080c044202626010808e868c4c0381a108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c0406025111098910602840441c0a0c05444483815011210104c488404210109890840470302120188808404424021011c0c04c48480a5141109004602210113120840545042624131208404848021014941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301109000c0484801312098800c04262403012120084804240428280c080604840441c1210110a0a83824202a10100604030264c480c080604420230b0108099312616010b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042402624018100c088682030201810989042402120800e4006d24248404800a210108405001921011888a0030480821014006884046222800b9888a002d001515050840600282101282040048a080706080089c180a081001328201c182002070602420400389080282080068a0809081000f24200a082001828200301400280c0426228004898880c05000b03010988a0010262221204001806022624800280c048481000721200989200082624018140008060421208000884800605000301810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_173 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_163 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2437 theta)
    · exact b4_2487 theta
    · exact b4_204 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_19 theta)
    · exact b4_2771 theta
    · exact b4_2794 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_173 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_163 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2437 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2487 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_173 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_163 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2437 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2487 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_173 theta)
    · exact b4_163 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2437 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2487 theta)
    · exact b4_3 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2832 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_223 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_204 theta)
    · exact b4_19 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2771 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2794 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2832 theta)
    · exact b4_223 theta
theorem b3_288 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_288 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_288 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc37w152 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons stored67 (PetersenWireProjection.cons pc37w151 rfl)))))))))) (by decide +kernel)
theorem b3_289 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_289 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(1,true),(3,true))] s3_289 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons pc34w155 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w154 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_290 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_290 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,false),(7,true))] s3_290 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons pc34w158 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_291 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_291 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(5,false),(7,true))] s3_291 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons pc34w159 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_292 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_292 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,false),(5,true))] s3_292 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xf0f00000f0f00000f0f00000f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons pc34w160 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_293 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_293 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true)),(false,(3,true),(5,false))] s3_293 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0xf0f00000f0f00000f0f00000f0f0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w156 (PetersenWireProjection.cons pc34w161 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
