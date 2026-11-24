import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc26w3 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl

private theorem pc26w2 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w3 stored2 rfl rfl




private theorem pc26w10 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc26w12 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 pc26w10 pc26w12 rfl rfl
private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w3 stored3 rfl rfl
private theorem pc26w15 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xffff0000ffff0000 := PetersenWireProjection.derive 2 stored2 stored6 rfl rfl
private theorem pc26w14 : PetersenPackedPin.project extra26 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xffffffff00000000ffffffffffff0000 := PetersenWireProjection.derive 3 pc26w15 stored4 rfl rfl
private theorem pc26w16 : PetersenPackedPin.project extra26 (0xffccffccffccffccff00ff00ff00ff00ffccffccffccffccff00ff00ff00ff00 : BitVec 256) = 0xffffffffaaaa0000ffffffffaaaa0000 := PetersenWireProjection.derive 3 pc26w3 stored4 rfl rfl
private theorem pc26w17 : PetersenPackedPin.project extra26 (0xfcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0fcfcfcfcfcfcfcfcf0f0f0f0f0f0f0f0 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc26w3 stored5 rfl rfl
private theorem pc26w19 : PetersenPackedPin.project extra26 (0xcccccccc000000000000000000000000cccccccc : BitVec 256) = 0x5555000055550000 := PetersenWireProjection.derive 1 pc26w15 stored1 rfl rfl
private theorem pc26w18 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaeeeeeeee : BitVec 256) = 0xf5f5f0f0f5f5f0f0 := PetersenWireProjection.derive 3 pc26w9 pc26w19 rfl rfl
private theorem pc26w22 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w21 : PetersenPackedPin.project extra26 (0x33333333000000000000000000000000333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa := PetersenWireProjection.derive 2 pc26w22 stored1 rfl rfl
private theorem pc26w20 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaabbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0fafaf0f0fafa := PetersenWireProjection.derive 3 pc26w9 pc26w21 rfl rfl
private theorem pc26w24 : PetersenPackedPin.project extra26 (0xcccccccc000000000000000000000000cccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc26w15 stored1 rfl rfl
private theorem pc26w23 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w9 pc26w24 rfl rfl
private theorem pc26w25 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccc0000000000000000 : BitVec 256) = 0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0 := PetersenWireProjection.derive 3 pc26w3 stored0 rfl rfl
private theorem pc26w28 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl
private theorem pc26w27 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 pc26w28 stored0 rfl rfl
private theorem pc26w26 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee : BitVec 256) = 0xfffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc26w27 pc26w12 rfl rfl
private theorem pc26w29 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w32 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl
private theorem pc26w31 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w32 stored0 rfl rfl
private theorem pc26w30 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafa := PetersenWireProjection.derive 1 pc26w31 pc26w12 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc26w35 stored2 rfl rfl
private theorem pc26w33 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaeeeeeeee : BitVec 256) = 0xfffffafafffffafa := PetersenWireProjection.derive 3 pc26w9 pc26w34 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 pc26w38 pc26w28 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffeeeeeeeeffffffffaaaaaaaaaaaaaaaaeeeeeeeeeeeeeeee : BitVec 256) = 0x5555000055550000f5f5f0f0f5f5f0f0 := PetersenWireProjection.derive 3 pc26w37 pc26w39 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0x5555555500000000000000000000000055555555000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 pc26w12 stored1 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffffffffffffffffffaaaaaaaaeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0x5555505055555050fffff0f0fffff0f0 := PetersenWireProjection.derive 2 pc26w41 pc26w27 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w43 stored3 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0x22222222222222222222222222222222 := PetersenWireProjection.derive 1 stored1 stored3 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0x33330000ffff0000000000000000000033330000ffff0000000000000000 : BitVec 256) = 0x2222000022222222222222222222 := PetersenWireProjection.derive 1 pc26w46 pc26w43 rfl rfl
private theorem pc26w44 : PetersenPackedPin.project extra26 (0xaaaabbbbaaaaffffaaaaaaaaaaaaaaaaaaaabbbbaaaaffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x2222000022222222222222222222 := PetersenWireProjection.derive 3 pc26w45 stored7 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffffffffffffffffcccccccccccccccc := PetersenWireProjection.derive 3 stored2 stored3 rfl rfl
private theorem pc26w47 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000 : BitVec 256) = 0xddddddddddddddddcccccccccccccccc := PetersenWireProjection.derive 2 pc26w46 pc26w48 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff00000000 : BitVec 256) = 0x55555555555555550000000000000000 := PetersenWireProjection.derive 2 stored1 stored2 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0x33330000333300003333000033330000 := PetersenWireProjection.derive 2 stored3 stored6 rfl rfl
private theorem pc26w50 : PetersenPackedPin.project extra26 (0xcccc0000cccc000000000000cccc0000cccc0000cccc000000000000cccc : BitVec 256) = 0x22220000222200003333000033330000 := PetersenWireProjection.derive 2 pc26w51 pc26w52 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeeeaaaaeeeeaaaaeeeeaaaaaaaaaaaaeeee : BitVec 256) = 0x22220000222200003333000033330000 := PetersenWireProjection.derive 3 pc26w50 stored7 rfl rfl
private theorem pc26w54 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w54 stored3 rfl rfl
private theorem pc26w56 : PetersenPackedPin.project extra26 (0xffff0000ffff000000000000000000003333000033330000000000000000 : BitVec 256) = 0x20202222202022222020222220202222 := PetersenWireProjection.derive 2 pc26w54 pc26w46 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0xaaaaffffaaaaffffaaaaaaaaaaaaaaaaaaaabbbbaaaabbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0x20202222202022222020222220202222 := PetersenWireProjection.derive 3 pc26w56 stored7 rfl rfl
private theorem pc26w58 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfffffafafffffafafffffafafffffafa := PetersenWireProjection.derive 3 pc26w35 stored0 rfl rfl
private theorem pc26w59 : PetersenPackedPin.project extra26 (0x3333000033330000333300003333000033330000333300003333000033330000 : BitVec 256) = 0xcccc0000cccc0000cccc0000cccc := PetersenWireProjection.derive 1 stored3 stored6 rfl rfl
private theorem pc26w57 : PetersenPackedPin.project extra26 (0xccccffffccccffffccccffffccccffffccccffffccccffffcccccccccccccccc : BitVec 256) = 0xffff3232ffff3232ffff3232ffff3232 := PetersenWireProjection.derive 1 pc26w58 pc26w59 rfl rfl
private theorem pc26w61 : PetersenPackedPin.project extra26 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 1 stored3 stored7 rfl rfl
private theorem pc26w60 : PetersenPackedPin.project extra26 (0xaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaaaaaaaaaaaaa : BitVec 256) = 0x32323232323232323232323232323232 := PetersenWireProjection.derive 1 pc26w31 pc26w61 rfl rfl
private theorem pc26w63 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored4 rfl rfl
private theorem pc26w64 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa := PetersenWireProjection.derive 1 stored1 stored4 rfl rfl
private theorem pc26w62 : PetersenPackedPin.project extra26 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xffffffff50505050ffffffff50505050 := PetersenWireProjection.derive 1 pc26w63 pc26w64 rfl rfl




private theorem pc26w70 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w22 stored1 rfl rfl
private theorem pc26w71 : PetersenPackedPin.project extra26 (0x3300330033003300330033003300330033003300330033003300330033003300 : BitVec 256) = 0xffff000000000000ffff00000000 := PetersenWireProjection.derive 1 stored4 stored6 rfl rfl
private theorem pc26w69 : PetersenPackedPin.project extra26 (0xccffccffccffccffccffccffccccccccccffccffccffccffccffccffcccccccc : BitVec 256) = 0xffff0000ffffffffffff0000ffffaaaa := PetersenWireProjection.derive 1 pc26w70 pc26w71 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl
private theorem pc26w73 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w74 stored1 rfl rfl
private theorem pc26w75 : PetersenPackedPin.project extra26 (0x5500550055005500550055005500550055005500550055005500550055005500 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored4 stored7 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0xaaffaaffaaffaaffaaffaaffaaaaaaaaaaffaaffaaffaaffaaffaaffaaaaaaaa : BitVec 256) = 0xffffffff00000000aaaaaaaa := PetersenWireProjection.derive 1 pc26w73 pc26w75 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored6 stored7 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0xbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaabbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 pc26w32 pc26w78 rfl rfl
private theorem pc26w76 : PetersenPackedPin.project extra26 (0xbbbbbbbbffffffffaaaaaaaaffffffffbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaa0000aaaaf0f0fafaf0f0fafa := PetersenWireProjection.derive 3 pc26w77 pc26w39 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xaaaaaaaaffffffffaaaaaaaaaaaaaaaaaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 pc26w32 pc26w12 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w79 : PetersenPackedPin.project extra26 (0xbbbbbbbbffffffffbbbbbbbbbbbbbbbbaaaaaaaaffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f00000f0f0aaaafafaaaaafafa := PetersenWireProjection.derive 3 pc26w80 pc26w81 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0x4444444400000000444444440000000044444444000000004444444400000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 pc26w78 stored2 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0xbbbbbbbbffffffffbbbbbbbbffffffffbbbbbbbbffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafa0000fafafafafafafafafafa := PetersenWireProjection.derive 1 pc26w31 pc26w83 rfl rfl






private theorem pc3w91 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w90 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc : BitVec 256) = 0xffffcccc := PetersenWireProjection.derive 3 pc3w91 stored34 rfl rfl

private theorem pc3w93 : PetersenPackedPin.project cycle3 (0x3300330033003300330033003300330033003300330033003300330033003300 : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 1 stored37 stored39 rfl rfl
private theorem pc3w89 : PetersenPackedPin.project cycle3 (0xccffccffccffccffccffccffccccccccccffccffccffccffccffccffcccccccc : BitVec 256) = 0x55554444 := PetersenWireProjection.derive 1 pc3w90 pc3w93 rfl rfl
private theorem pc3w97 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w96 : PetersenPackedPin.project cycle3 (0xcccccccc000000000000000000000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc3w97 stored34 rfl rfl
private theorem pc3w98 : PetersenPackedPin.project cycle3 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored37 stored39 rfl rfl
private theorem pc3w95 : PetersenPackedPin.project cycle3 (0xcc00cc00cc00cc00cc00cc00cccccccccc00cc00cc00cc00cc00cc00cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w96 pc3w98 rfl rfl

private theorem pc3w101 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xfafafafa := PetersenWireProjection.derive 3 stored33 stored37 rfl rfl
private theorem pc3w102 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0x55550000 := PetersenWireProjection.derive 1 stored34 stored37 rfl rfl
private theorem pc3w100 : PetersenPackedPin.project cycle3 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 1 pc3w101 pc3w102 rfl rfl
private theorem pc3w105 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored34 stored39 rfl rfl
private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc3w105 stored33 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xcc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w104 pc3w98 rfl rfl
private theorem pc3w107 : PetersenPackedPin.project cycle3 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0 := PetersenWireProjection.derive 1 stored33 stored34 rfl rfl
private theorem pc3w108 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored37 stored39 rfl rfl
private theorem pc3w106 : PetersenPackedPin.project cycle3 (0xffccffccffccffccffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaafafa := PetersenWireProjection.derive 3 pc3w107 pc3w108 rfl rfl




private theorem pc17w114 : PetersenPackedPin.project tree17 (0xffffffffffffffff00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored169 stored170 rfl rfl


private theorem pc17w115 : PetersenPackedPin.project tree17 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored173 stored175 rfl rfl
private theorem pc17w113 : PetersenPackedPin.project tree17 (0xffccffccffccffccffffffffffffffffffccffccffccffccffccffccffccffcc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 pc17w114 pc17w115 rfl rfl
private theorem pc17w119 : PetersenPackedPin.project tree17 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored169 stored173 rfl rfl
private theorem pc17w120 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored170 stored173 rfl rfl
private theorem pc17w118 : PetersenPackedPin.project tree17 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc17w119 pc17w120 rfl rfl

private theorem pc17w124 : PetersenPackedPin.project tree17 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xc0c0c0c0c0c0c0c := PetersenWireProjection.derive 2 stored170 stored175 rfl rfl
private theorem pc17w123 : PetersenPackedPin.project tree17 (0xcccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc17w124 stored169 rfl rfl
private theorem pc17w125 : PetersenPackedPin.project tree17 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored173 stored175 rfl rfl
private theorem pc17w122 : PetersenPackedPin.project tree17 (0xcc00cc00cc00cc00cccccccccccccccccc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc17w123 pc17w125 rfl rfl






private theorem pc2w132 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 2 stored43 stored47 rfl rfl

private theorem pc2w131 : PetersenPackedPin.project cycle2 (0xff00ff00ffccffccff00ff00ffccffccff00ff00ffccffccff00ff00ffccffcc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w132 stored45 rfl rfl

private theorem pc2w138 : PetersenPackedPin.project cycle2 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored45 stored47 rfl rfl
private theorem pc2w137 : PetersenPackedPin.project cycle2 (0xcc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w132 pc2w138 rfl rfl
private theorem pc2w139 : PetersenPackedPin.project cycle2 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a := PetersenWireProjection.derive 2 stored41 stored47 rfl rfl
private theorem pc2w136 : PetersenPackedPin.project cycle2 (0xcc00cc00cccccccccc00cc00cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w137 pc2w139 rfl rfl

private theorem pc3w142 : PetersenPackedPin.project cycle3 (0xcc00cc00cccccccccc00cc00cccccccccc00cc00cccccccccc00cc00cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w97 pc3w98 rfl rfl
private theorem pc3w141 : PetersenPackedPin.project cycle3 (0xcc00cc00cccccccccccccccccccccccccc00cc00cccccccccc00cc00cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w104 pc3w142 rfl rfl
private theorem pc2w144 : PetersenPackedPin.project cycle2 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0xaaaa := PetersenWireProjection.derive 2 stored42 stored47 rfl rfl
private theorem pc2w143 : PetersenPackedPin.project cycle2 (0xcc00cc00cccccccccccccccccccccccccc00cc00cccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 pc2w137 pc2w144 rfl rfl
private theorem pc17w146 : PetersenPackedPin.project tree17 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x3333000033330000 := PetersenWireProjection.derive 1 stored171 stored175 rfl rfl
private theorem pc17w145 : PetersenPackedPin.project tree17 (0xcc00cc00ff00ff00ccccccccffffffffcc00cc00ff00ff00cc00cc00ff00ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc17w118 pc17w146 rfl rfl







private theorem pc0w155 : PetersenPackedPin.project cycle0 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xcccc0000 := PetersenWireProjection.derive 0 stored51 stored55 rfl rfl
private theorem pc0w154 : PetersenPackedPin.project cycle0 (0xcccccccc000000000000000000000000cccccccc000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc0w155 stored50 rfl rfl

private theorem pc0w158 : PetersenPackedPin.project cycle0 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 stored49 stored51 rfl rfl
private theorem pc0w157 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffff0000000000000000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 3 pc0w158 stored50 rfl rfl
private theorem pc0w160 : PetersenPackedPin.project cycle0 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 2 stored49 stored55 rfl rfl
private theorem pc0w159 : PetersenPackedPin.project cycle0 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcc00cc := PetersenWireProjection.derive 3 pc0w160 stored52 rfl rfl
private theorem pc0w162 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored52 rfl rfl
private theorem pc0w163 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored52 rfl rfl
private theorem pc0w161 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xff000000 := PetersenWireProjection.derive 0 pc0w162 pc0w163 rfl rfl
private theorem pc0w165 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored53 rfl rfl
private theorem pc0w166 : PetersenPackedPin.project cycle0 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored50 stored53 rfl rfl
private theorem pc0w164 : PetersenPackedPin.project cycle0 (0xff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 1 pc0w165 pc0w166 rfl rfl
theorem b4_2562 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2562 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,false),(1,false)),(false,(0,true),(8,true))] s4_2562 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2563 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2563 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(1,false),(5,false)),(false,(3,true),(0,true))] s4_2563 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2564 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2564 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,false),(7,true)),(false,(1,true),(7,true))] s4_2564 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffffffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2565 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2565 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(1,false),(5,false)),(false,(0,true),(7,true))] s4_2565 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffaaaa0000ffffffffaaaa0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w16 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2566 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2566 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,false),(1,false)),(false,(5,true),(0,true))] s4_2566 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w9 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2567 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2567 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(3,true)),(false,(0,true),(8,true))] s4_2567 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf5f5f0f0f5f5f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w18 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2568 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2568 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true)),(false,(0,true),(3,true)),(false,(0,true),(8,true))] s4_2568 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0fafaf0f0fafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w20 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2569 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2569 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true)),(false,(0,true),(8,true))] s4_2569 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafaf0f0fafaf0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2570 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2570 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(3,true)),(false,(8,true),(0,true))] s4_2570 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafaf0f0fafaf0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w23 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w25 rfl))))))))) (by decide +kernel)
theorem b4_2571 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2571 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(3,false),(7,true)),(false,(1,true),(0,true))] s4_2571 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0fffff0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2572 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2572 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,true),(7,true)),(false,(6,true),(8,true))] s4_2572 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0fffff0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2573 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2573 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(0,true),(7,true)),(false,(6,true),(8,true))] s4_2573 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0fffff0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w22 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w29 rfl))))))))) (by decide +kernel)
theorem b4_2574 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2574 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,false),(7,true)),(false,(1,true),(0,true))] s4_2574 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w30 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2575 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2575 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(2,true)),(false,(0,false),(1,true)),(false,(0,true),(8,true))] s4_2575 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffffafafffffafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w33 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2576 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2576 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(5,false),(1,true)),(false,(1,true),(0,true))] s4_2576 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x5555000055550000f5f5f0f0f5f5f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2577 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2577 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false)),(false,(5,true),(3,true)),(false,(1,true),(0,true))] s4_2577 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x5555505055555050fffff0f0fffff0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2578 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2578 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(2,true)),(false,(0,false),(2,false))] s4_2578 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x2222000022222222222222222222,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w44 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w42 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2579 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2579 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(2,true)),(false,(0,false),(6,false))] s4_2579 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x22220000222200003333000033330000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xddddddddddddddddcccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w47 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2580 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2580 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true)),(false,(0,false),(2,false))] s4_2580 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x20202222202022222020222220202222,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2581 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2581 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true)),(false,(2,true),(0,true)),(false,(0,true),(6,true))] s4_2581 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x32323232323232323232323232323232,0xffff0000ffff0000ffff0000ffff0000,0xffff3232ffff3232ffff3232ffff3232,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w60 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w57 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2582 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2582 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true)),(false,(0,false),(6,false))] s4_2582 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xafaf000000000000afaf0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored282 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2583 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2583 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(6,true)),(false,(0,false),(8,false))] s4_2583 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xafafafaf0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff50505050ffffffff50505050,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored283 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2584 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2584 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(6,true)),(false,(0,false),(2,false))] s4_2584 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa000000000000aaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffffffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored284 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2585 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2585 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,true)),(false,(0,true),(6,true)),(false,(0,false),(4,false))] s4_2585 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f0f0f0000000000000f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffffffff0000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored285 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons pc26w14 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2586 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2586 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true)),(false,(6,true),(0,true)),(false,(0,true),(6,true))] s4_2586 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffffffff00000000aaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffffffffffff0000ffffaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w72 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2587 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2587 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(1,false),(5,true)),(false,(1,true),(0,true))] s4_2587 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaa0000aaaaf0f0fafaf0f0fafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2588 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2588 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(3,false),(5,true)),(false,(1,true),(0,true))] s4_2588 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xf0f00000f0f0aaaafafaaaaafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2589 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2589 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(1,true),(3,true)),(false,(1,true),(0,true))] s4_2589 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfafa0000fafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b4_2590 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2590 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(1,true)),(false,(1,true),(0,true))] s4_2590 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x55554444,0x0,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w95 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons pc3w89 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2591 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2591 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2591 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w103 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w100 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2592 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2592 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2592 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w103 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w106 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2593 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2593 := by
  intro m le c
  apply rejects_sound tree17 i6 6 tgt small17 hot17 [] s4_2593 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xffffffff00000000,0x0,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons stored176 (PetersenWireProjection.cons pc17w122 (PetersenWireProjection.cons stored174 (PetersenWireProjection.cons pc17w118 (PetersenWireProjection.cons pc17w113 (PetersenWireProjection.cons stored172 (PetersenWireProjection.cons stored171 (PetersenWireProjection.cons stored170 (PetersenWireProjection.cons stored169 rfl))))))))) (by decide +kernel)
theorem b4_2594 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2594 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2594 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w136 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w131 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2595 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2595 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2595 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w136 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w131 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl)))))))) (by decide +kernel)
theorem b4_2596 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2596 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(2,false),(4,true)),(false,(0,true),(1,true))] s4_2596 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaafafa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons pc3w141 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons pc3w100 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b4_2597 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2597 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s4_2597 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xaaaaaaaa,0xcccccccc,0xaaaaaaaa,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons pc2w143 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons pc2w131 (PetersenWireProjection.cons stored44 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b4_2598 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2598 := by
  intro m le c
  apply rejects_sound tree17 i6 6 tgt small17 hot17 [] s4_2598 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc,0xffffffff00000000,0x0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xf0f0f0f0f0f0f0f0,0x0] (PetersenWireProjection.cons stored176 (PetersenWireProjection.cons pc17w145 (PetersenWireProjection.cons stored175 (PetersenWireProjection.cons stored174 (PetersenWireProjection.cons pc17w118 (PetersenWireProjection.cons stored172 (PetersenWireProjection.cons stored171 (PetersenWireProjection.cons stored170 (PetersenWireProjection.cons stored169 rfl))))))))) (by decide +kernel)
theorem b4_2599 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2599 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2599 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2600 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2600 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(4,false),(3,false))] s4_2600 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xff000000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w157 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2601 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2601 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(1,false),(3,true))] s4_2601 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xcc00cc,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w159 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2602 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2602 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [(false,(3,false),(4,false))] s4_2602 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0x0,0xffff0000,0xff000000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w161 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b4_2603 (theta : Extra1020K12.Theta) : Blocked tgt 8 s4_2603 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s4_2603 8 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0x0,0xcccccccc,0xf0f0f0f0,0xff00ff00,0x0,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons pc0w154 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons pc0w164 (PetersenWireProjection.cons stored52 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
