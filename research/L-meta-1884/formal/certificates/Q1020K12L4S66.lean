import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc3w1 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl

private theorem pc3w0 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffff00000000cccccccc00000000cccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w1 stored33 rfl rfl




private theorem pc3w10 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored33 stored39 rfl rfl
private theorem pc3w11 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w9 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w10 pc3w11 rfl rfl

private theorem pc3w14 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w13 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc3w14 stored33 rfl rfl
private theorem pc3w16 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w1 stored33 rfl rfl
private theorem pc3w15 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffffccccffff0000ffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w16 stored36 rfl rfl
private theorem pc3w18 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w17 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w18 stored36 rfl rfl
private theorem pc3w19 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w14 stored36 rfl rfl






private theorem pc61w27 : PetersenPackedPin.project extra61 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored287 stored291 rfl rfl
private theorem pc61w29 : PetersenPackedPin.project extra61 (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored288 stored291 rfl rfl
private theorem pc61w26 : PetersenPackedPin.project extra61 (0xf0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc61w27 pc61w29 rfl rfl
private theorem pc61w30 : PetersenPackedPin.project extra61 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored286 stored291 rfl rfl
private theorem pc61w25 : PetersenPackedPin.project extra61 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc61w26 pc61w30 rfl rfl

private theorem pc61w33 : PetersenPackedPin.project extra61 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored286 stored292 rfl rfl
private theorem pc61w34 : PetersenPackedPin.project extra61 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored288 stored292 rfl rfl
private theorem pc61w32 : PetersenPackedPin.project extra61 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc61w33 pc61w34 rfl rfl

private theorem pc3w37 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored38 rfl rfl
private theorem pc3w38 : PetersenPackedPin.project cycle3 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored38 rfl rfl
private theorem pc3w36 : PetersenPackedPin.project cycle3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0000 := PetersenWireProjection.derive 2 pc3w37 pc3w38 rfl rfl
private theorem pc3w39 : PetersenPackedPin.project cycle3 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w14 stored38 rfl rfl







private theorem pc74w48 : PetersenPackedPin.project extra74 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored115 stored119 rfl rfl
private theorem pc74w47 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 pc74w48 stored113 rfl rfl
private theorem pc74w50 : PetersenPackedPin.project extra74 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 stored114 stored119 rfl rfl
private theorem pc74w46 : PetersenPackedPin.project extra74 (0xccccccccccccccccffffffffffffffffccccccccccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc74w47 pc74w50 rfl rfl
private theorem pc74w52 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored113 stored119 rfl rfl
private theorem pc74w53 : PetersenPackedPin.project extra74 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored115 stored119 rfl rfl
private theorem pc74w51 : PetersenPackedPin.project extra74 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc74w52 pc74w53 rfl rfl




private theorem pc73w58 : PetersenPackedPin.project extra73 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored131 stored135 rfl rfl
private theorem pc73w57 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xeeeeeeeeeeeeeeee := PetersenWireProjection.derive 3 pc73w58 stored129 rfl rfl

private theorem pc73w61 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w56 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc73w57 pc73w61 rfl rfl



private theorem pc73w67 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored129 stored135 rfl rfl
private theorem pc73w68 : PetersenPackedPin.project extra73 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored131 stored135 rfl rfl
private theorem pc73w66 : PetersenPackedPin.project extra73 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w67 pc73w68 rfl rfl

private theorem pc3w70 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 stored33 stored35 rfl rfl







private theorem pc0w80 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored50 stored55 rfl rfl
private theorem pc0w81 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w79 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccccccccccccccccccc00000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc0w80 pc0w81 rfl rfl
private theorem pc0w82 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xcc00cc00 := PetersenWireProjection.derive 0 stored49 stored55 rfl rfl
private theorem pc0w78 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc0w79 pc0w82 rfl rfl








private theorem pc69w93 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored97 stored100 rfl rfl
private theorem pc69w94 : PetersenPackedPin.project extra69 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored99 stored100 rfl rfl
private theorem pc69w92 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w93 pc69w94 rfl rfl
private theorem pc69w96 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored98 stored99 rfl rfl
private theorem pc69w95 : PetersenPackedPin.project extra69 (0xffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w96 stored97 rfl rfl
private theorem pc69w91 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccccccccccc00000000ffffffff00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w92 pc69w95 rfl rfl

private theorem pc3w99 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored38 rfl rfl
private theorem pc3w98 : PetersenPackedPin.project cycle3 (0xfffffffff0f0f0f0f0f0f0f0f0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 pc3w38 pc3w99 rfl rfl
private theorem pc3w102 : PetersenPackedPin.project cycle3 (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored38 stored39 rfl rfl
private theorem pc3w101 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w10 pc3w102 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w11 stored34 rfl rfl
private theorem pc3w100 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w101 pc3w103 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w10 stored37 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xeeeeeeee := PetersenWireProjection.derive 3 stored35 stored37 rfl rfl
private theorem pc3w106 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffffffffffff00ff00ffffffffff00ff00 : BitVec 256) = 0xfefefefe := PetersenWireProjection.derive 3 pc3w107 stored33 rfl rfl
private theorem pc3w105 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccc00cc00cccccccccc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w106 stored39 rfl rfl
private theorem pc3w109 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xf3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0f3f3f3f3f0f0f0f0 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w109 stored38 rfl rfl
private theorem pc3w110 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w10 pc3w14 rfl rfl
private theorem pc61w112 : PetersenPackedPin.project extra61 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc61w27 stored286 rfl rfl
private theorem pc61w113 : PetersenPackedPin.project extra61 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored288 stored291 rfl rfl
private theorem pc61w111 : PetersenPackedPin.project extra61 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0f0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 0 pc61w112 pc61w113 rfl rfl
private theorem pc61w115 : PetersenPackedPin.project extra61 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored287 stored292 rfl rfl
private theorem pc61w114 : PetersenPackedPin.project extra61 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc61w33 pc61w115 rfl rfl
private theorem pc3w117 : PetersenPackedPin.project cycle3 (0xccccccccccccccccc0c0c0c0c0c0c0c0ccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w14 pc3w102 rfl rfl
private theorem pc3w116 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccccccccccccccccccc0c0c0c0c0c0c0c0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w117 pc3w10 rfl rfl
private theorem pc3w119 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccc00000000cccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w14 pc3w11 rfl rfl
private theorem pc3w118 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w119 pc3w10 rfl rfl







private theorem pc2w128 : PetersenPackedPin.project cycle2 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored42 stored47 rfl rfl
private theorem pc2w130 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w127 : PetersenPackedPin.project cycle2 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w128 pc2w130 rfl rfl
private theorem pc2w131 : PetersenPackedPin.project cycle2 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x50505050 := PetersenWireProjection.derive 1 stored41 stored47 rfl rfl
private theorem pc2w126 : PetersenPackedPin.project cycle2 (0xccccccccccccccccccccccccccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 pc2w127 pc2w131 rfl rfl

private theorem pc73w135 : PetersenPackedPin.project extra73 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored130 stored131 rfl rfl
private theorem pc73w134 : PetersenPackedPin.project extra73 (0xffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w135 stored129 rfl rfl
private theorem pc73w133 : PetersenPackedPin.project extra73 (0xccccccccccccccccccccccccccccccccccccccccffffffffcccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w66 pc73w134 rfl rfl
private theorem pc0w138 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl
private theorem pc0w139 : PetersenPackedPin.project cycle0 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33330000 := PetersenWireProjection.derive 1 stored51 stored55 rfl rfl
private theorem pc0w137 : PetersenPackedPin.project cycle0 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc0w138 pc0w139 rfl rfl
private theorem pc0w140 : PetersenPackedPin.project cycle0 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33003300 := PetersenWireProjection.derive 1 stored49 stored55 rfl rfl
private theorem pc0w136 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc0w137 pc0w140 rfl rfl
private theorem pc69w142 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored99 rfl rfl
private theorem pc69w141 : PetersenPackedPin.project extra69 (0xffffffffffffffffffffffffffffffffffffffff000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 pc69w142 stored97 rfl rfl
private theorem pc69w144 : PetersenPackedPin.project extra69 (0xffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc69w142 stored97 rfl rfl
private theorem pc69w143 : PetersenPackedPin.project extra69 (0xccccccccccccccccccccccccccccccccffffffff000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w144 pc69w93 rfl rfl
private theorem pc69w145 : PetersenPackedPin.project extra69 (0xccccccccccccccccccccccccccccccccffffffff00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w92 pc69w144 rfl rfl
private theorem pc69w148 : PetersenPackedPin.project extra69 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored98 stored100 rfl rfl
private theorem pc69w147 : PetersenPackedPin.project extra69 (0xcccccccccccccccccccccccccccccccccccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w93 pc69w148 rfl rfl
private theorem pc69w146 : PetersenPackedPin.project extra69 (0xccccccccccccccccccccccccccccccccffffffffcccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc69w147 pc69w144 rfl rfl
private theorem pc0w151 : PetersenPackedPin.project cycle0 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 stored51 stored55 rfl rfl
private theorem pc0w150 : PetersenPackedPin.project cycle0 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 0 pc0w138 pc0w151 rfl rfl
private theorem pc0w149 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 pc0w150 pc0w140 rfl rfl
private theorem pc2w152 : PetersenPackedPin.project cycle2 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 pc2w131 pc2w130 rfl rfl
private theorem pc3w154 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w155 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w153 : PetersenPackedPin.project cycle3 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xc0c0c0c := PetersenWireProjection.derive 2 pc3w154 pc3w155 rfl rfl



private theorem pc75w159 : PetersenPackedPin.project extra75 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0x3030303030303030 := PetersenWireProjection.derive 1 stored209 stored212 rfl rfl
private theorem pc75w161 : PetersenPackedPin.project extra75 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored210 stored212 rfl rfl
private theorem pc75w158 : PetersenPackedPin.project extra75 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 2 pc75w159 pc75w161 rfl rfl




private theorem pc75w166 : PetersenPackedPin.project extra75 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored209 stored211 rfl rfl
private theorem pc75w168 : PetersenPackedPin.project extra75 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored212 stored211 rfl rfl
private theorem pc75w165 : PetersenPackedPin.project extra75 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 2 pc75w166 pc75w168 rfl rfl

private theorem pc3w170 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w14 stored35 rfl rfl
private theorem pc3w171 : PetersenPackedPin.project cycle3 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc3w14 stored37 rfl rfl
private theorem pc75w173 : PetersenPackedPin.project extra75 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored209 stored215 rfl rfl
private theorem pc75w174 : PetersenPackedPin.project extra75 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 3 stored210 stored215 rfl rfl
private theorem pc75w172 : PetersenPackedPin.project extra75 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 2 pc75w173 pc75w174 rfl rfl
private theorem pc73w175 : PetersenPackedPin.project extra73 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 pc73w61 stored129 rfl rfl
private theorem pc73w177 : PetersenPackedPin.project extra73 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored129 stored130 rfl rfl
private theorem pc73w176 : PetersenPackedPin.project extra73 (0xccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc73w177 pc73w67 rfl rfl


private theorem pc30w178 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl

private theorem pc30w181 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl



private theorem pc30w187 : PetersenPackedPin.project extra30 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f0 := PetersenWireProjection.derive 2 stored8 stored9 rfl rfl

private theorem pc30w188 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff0000000000 := PetersenWireProjection.derive 0 stored8 stored14 rfl rfl
private theorem pc30w186 : PetersenPackedPin.project extra30 (0xccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00f0f0f0f0ff00ff00f0f0f0f0 := PetersenWireProjection.derive 3 pc30w187 pc30w188 rfl rfl



private theorem pc34w191 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl

private theorem pc34w194 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl



private theorem pc34w200 : PetersenPackedPin.project extra34 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored16 stored17 rfl rfl

private theorem pc34w201 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w199 : PetersenPackedPin.project extra34 (0xccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaffff0000ffff0000 := PetersenWireProjection.derive 3 pc34w200 pc34w201 rfl rfl

private theorem pc74w204 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored113 stored114 rfl rfl
private theorem pc74w205 : PetersenPackedPin.project extra74 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored114 stored115 rfl rfl
private theorem pc74w207 : PetersenPackedPin.project extra74 (0xffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 2 stored113 stored114 rfl rfl
private theorem pc74w206 : PetersenPackedPin.project extra74 (0xccccccccccccccccccccccccccccccccffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f := PetersenWireProjection.derive 3 pc74w207 pc74w52 rfl rfl
private theorem pc0w208 : PetersenPackedPin.project cycle0 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 pc0w140 pc0w138 rfl rfl
private theorem pc0w209 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl
theorem b4_2772 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2772 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2772 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w0 rfl))))))))) (by decide +kernel)
theorem b4_2773 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2773 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2773 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w13 rfl))))))))) (by decide +kernel)
theorem b4_2774 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2774 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2774 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w15 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2775 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2775 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2775 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2776 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2776 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2776 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w19 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2777 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2777 := by
  intro m le c
  apply rejects_sound extra61 i6 5 tgt small61 hot61 [] s4_2777 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0x0,0x0,0xffffffffffffffff,0xcccccccccccccccc,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored293 (PetersenWireProjection.cons pc61w32 (PetersenWireProjection.cons stored292 (PetersenWireProjection.cons pc61w25 (PetersenWireProjection.cons stored290 (PetersenWireProjection.cons stored289 (PetersenWireProjection.cons stored288 (PetersenWireProjection.cons stored287 (PetersenWireProjection.cons stored286 rfl))))))))) (by decide +kernel)
theorem b4_2778 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2778 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2778 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w36 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2779 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2779 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2779 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2780 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2780 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2780 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons pc74w51 (PetersenWireProjection.cons pc74w46 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons stored114 (PetersenWireProjection.cons stored113 rfl))))))))) (by decide +kernel)
theorem b4_2781 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2781 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2781 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons pc73w66 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons pc73w56 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2782 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2782 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,true),(1,true))] s4_2782 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xfcfcfcfc] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w9 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w0 (PetersenWireProjection.cons pc3w70 rfl))))))))) (by decide +kernel)
theorem b4_2783 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2783 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2783 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w78 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2784 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2784 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2784 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons pc69w91 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2785 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2785 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(4,false))] s4_2785 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccc0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w100 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w98 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2786 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2786 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2786 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w105 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w104 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2787 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2787 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2787 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xcccccccc,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w110 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w108 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2788 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2788 := by
  intro m le c
  apply rejects_sound extra61 i6 5 tgt small61 hot61 [] s4_2788 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0x0,0x0,0xcccccccccccccccc,0xff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffff00000000] (PetersenWireProjection.cons stored293 (PetersenWireProjection.cons pc61w114 (PetersenWireProjection.cons stored292 (PetersenWireProjection.cons stored290 (PetersenWireProjection.cons stored289 (PetersenWireProjection.cons stored288 (PetersenWireProjection.cons pc61w111 (PetersenWireProjection.cons stored287 (PetersenWireProjection.cons stored286 rfl))))))))) (by decide +kernel)
theorem b4_2789 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2789 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,false),(2,true))] s4_2789 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xf0f0000,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w116 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w36 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2790 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2790 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2790 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2791 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2791 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s4_2791 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w118 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w13 rfl))))))))) (by decide +kernel)
theorem b4_2792 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2792 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2792 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w126 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2793 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2793 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2793 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons pc73w133 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl))))))))) (by decide +kernel)
theorem b4_2794 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2794 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2794 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w136 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2795 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2795 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2795 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w143 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons pc69w141 rfl))))))))) (by decide +kernel)
theorem b4_2796 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2796 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2796 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w145 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2797 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2797 := by
  intro m le c
  apply rejects_sound extra69 i5 4 tgt small69 hot69 [] s4_2797 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xff00ff00,0xffff0000,0xcccccccc,0x0,0xaaaaaaaa,0xf0f0f0f0] (PetersenWireProjection.cons stored104 (PetersenWireProjection.cons stored100 (PetersenWireProjection.cons pc69w146 (PetersenWireProjection.cons stored103 (PetersenWireProjection.cons stored102 (PetersenWireProjection.cons stored101 (PetersenWireProjection.cons stored99 (PetersenWireProjection.cons stored98 (PetersenWireProjection.cons stored97 rfl))))))))) (by decide +kernel)
theorem b4_2798 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2798 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2798 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w149 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2799 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2799 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2799 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons pc2w152 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2800 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2800 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2800 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w13 rfl))))))))) (by decide +kernel)
theorem b4_2801 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2801 := by
  intro m le c
  apply rejects_sound extra75 i6 5 tgt small75 hot75 [] s4_2801 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xffffffffffffffff,0xffffffffffffffff,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored216 (PetersenWireProjection.cons stored211 (PetersenWireProjection.cons pc75w165 (PetersenWireProjection.cons stored215 (PetersenWireProjection.cons stored214 (PetersenWireProjection.cons stored213 (PetersenWireProjection.cons pc75w158 (PetersenWireProjection.cons stored210 (PetersenWireProjection.cons stored209 rfl))))))))) (by decide +kernel)
theorem b4_2802 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2802 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2802 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons pc3w170 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2803 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2803 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2803 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w17 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2804 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2804 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2804 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w19 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2805 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2805 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2805 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w171 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2806 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2806 := by
  intro m le c
  apply rejects_sound extra75 i6 5 tgt small75 hot75 [] s4_2806 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000,0xffffffffffffffff,0xffffffffffffffff,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00,0xcccccccccccccccc,0x0,0xf0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored216 (PetersenWireProjection.cons stored211 (PetersenWireProjection.cons pc75w165 (PetersenWireProjection.cons pc75w172 (PetersenWireProjection.cons stored214 (PetersenWireProjection.cons stored213 (PetersenWireProjection.cons stored212 (PetersenWireProjection.cons stored210 (PetersenWireProjection.cons stored209 rfl))))))))) (by decide +kernel)
theorem b4_2807 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2807 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,false),(2,true))] s4_2807 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xc0c0c0c,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w153 (PetersenWireProjection.cons pc3w39 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2808 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2808 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s4_2808 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00,0x0,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons pc73w176 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons pc73w175 rfl))))))))) (by decide +kernel)
theorem b4_2809 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2809 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(3,true)),(false,(6,true),(3,true)),(false,(1,true),(0,true))] s4_2809 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xff00ff00f0f0f0f0ff00ff00f0f0f0f0,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons pc30w186 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w181 (PetersenWireProjection.cons pc30w178 rfl))))))))) (by decide +kernel)
theorem b4_2810 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2810 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,true)),(false,(7,true),(5,true)),(false,(1,true),(0,true))] s4_2810 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons pc34w199 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w194 (PetersenWireProjection.cons pc34w191 rfl))))))))) (by decide +kernel)
theorem b4_2811 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2811 := by
  intro m le c
  apply rejects_sound extra74 i6 5 tgt small74 hot74 [] s4_2811 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xf0f0f0f0f0f0f0f,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000,0xcccccccccccccccc,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons stored120 (PetersenWireProjection.cons stored119 (PetersenWireProjection.cons pc74w206 (PetersenWireProjection.cons stored118 (PetersenWireProjection.cons stored117 (PetersenWireProjection.cons stored116 (PetersenWireProjection.cons stored115 (PetersenWireProjection.cons pc74w205 (PetersenWireProjection.cons pc74w204 rfl))))))))) (by decide +kernel)
theorem b4_2812 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2812 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2812 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w208 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2813 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2813 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2813 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons pc0w208 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w209 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
