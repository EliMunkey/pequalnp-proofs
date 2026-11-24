import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S5
import Q1020K12L4S6
import Q1020K12L4S7
import Q1020K12L4S11
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S19
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S23
import Q1020K12L4S24
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S29
import Q1020K12L4S33
import Q1020K12L4S35
import Q1020K12L4S36
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S40
import Q1020K12L4S41
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S47
import Q1020K12L4S49
import Q1020K12L4S53
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S59
import Q1020K12L4S61
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S68
import Q1020K12L4S70
import Q1020K12L4S71
import Q1020K12L4S72
import Q1020K12L4S73
import Q1020K12L4S74
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc41w1 : PetersenPackedPin.project extra41 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc := PetersenWireProjection.derive 3 stored89 stored95 rfl rfl

private theorem pc41w0 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc41w1 stored91 rfl rfl
private theorem pc41w5 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
private theorem pc41w6 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored95 rfl rfl







private theorem pc26w13 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl

private theorem pc26w12 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w13 stored0 rfl rfl

private theorem pc26w17 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl






private theorem pc30w24 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl

private theorem pc30w23 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w24 stored8 rfl rfl

private theorem pc30w28 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffff00ff00ffffffffff00ff00 := PetersenWireProjection.derive 3 stored8 stored14 rfl rfl




private theorem pc30w34 : PetersenPackedPin.project extra30 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 stored8 stored9 rfl rfl


private theorem pc34w35 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl

private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl

private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl




private theorem pc26w47 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w48 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 3 stored3 stored7 rfl rfl
private theorem pc26w46 : PetersenPackedPin.project extra26 (0xffffaaaaffffaaaaffffaaaaffffaaaaffffeeeeffffeeeeffffeeeeffffeeee : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w47 pc26w48 rfl rfl
private theorem pc26w49 : PetersenPackedPin.project extra26 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xcfcfcccccfcfcccccfcfcccccfcfcccc := PetersenWireProjection.derive 3 pc26w47 stored3 rfl rfl
private theorem pc34w50 : PetersenPackedPin.project extra34 (0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored19 stored22 rfl rfl
private theorem pc34w52 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored16 stored22 rfl rfl
private theorem pc34w51 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc34w52 stored19 rfl rfl
private theorem pc30w54 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xff00ff0000000000ff00ff00 := PetersenWireProjection.derive 2 stored8 stored14 rfl rfl
private theorem pc30w55 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored11 stored13 rfl rfl
private theorem pc30w53 : PetersenPackedPin.project extra30 (0xfffff0f0fffff0f0fffff0f0fffff0f0fffffcfcfffffcfcfffffcfcfffffcfc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w54 pc30w55 rfl rfl
private theorem pc30w56 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xffffffffffffffff00000000ff00ff00 := PetersenWireProjection.derive 3 pc30w54 stored11 rfl rfl




private theorem pc32w61 : PetersenPackedPin.project extra32 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 stored24 stored29 rfl rfl


private theorem pc32w63 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 3 stored27 stored28 rfl rfl
private theorem pc32w60 : PetersenPackedPin.project extra32 (0xffffff00ffffff00ffffff00ffffff00ffffffccffffffccffffffccffffffcc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w61 pc32w63 rfl rfl
private theorem pc32w66 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff0aff0aff0aff0aff0aff0aff0aff0a := PetersenWireProjection.derive 3 pc32w61 stored27 rfl rfl






private theorem pc3w71 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w75 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl

private theorem pc3w74 : PetersenPackedPin.project cycle3 (0xffff0000ffff0000ffff0000ffff0000ffffccccffffccccffffccccffffcccc : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w75 stored36 rfl rfl



private theorem pc3w80 : PetersenPackedPin.project cycle3 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored34 stored39 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl
private theorem pc3w82 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl
private theorem pc32w83 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl
private theorem pc34w85 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl
private theorem pc34w84 : PetersenPackedPin.project extra34 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 3 pc34w85 stored19 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffeeeeffffaaaaffffeeeeffffaaaaffffeeeeffffaaaaffffeeeeffffaaaa : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w87 pc26w48 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffccccffffcccccccccccccccccccc := PetersenWireProjection.derive 3 pc26w87 stored3 rfl rfl
private theorem pc30w90 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl
private theorem pc30w89 : PetersenPackedPin.project extra30 (0xfffffcfcfffff0f0fffffcfcfffff0f0fffffcfcfffff0f0fffffcfcfffff0f0 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w90 pc30w55 rfl rfl
private theorem pc30w91 : PetersenPackedPin.project extra30 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xffffffffffffffffaa00aa00aa00aa00 := PetersenWireProjection.derive 3 pc30w90 stored11 rfl rfl




private theorem pc2w94 : PetersenPackedPin.project cycle2 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xaaaaaaaa := PetersenWireProjection.derive 3 stored43 stored47 rfl rfl
private theorem pc2w98 : PetersenPackedPin.project cycle2 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored43 stored47 rfl rfl

private theorem pc2w97 : PetersenPackedPin.project cycle2 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc2w98 stored44 rfl rfl



private theorem pc3w104 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored35 stored39 rfl rfl
private theorem pc3w103 : PetersenPackedPin.project cycle3 (0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w104 stored36 rfl rfl
private theorem pc2w105 : PetersenPackedPin.project cycle2 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored42 stored43 rfl rfl
private theorem pc34w107 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w106 : PetersenPackedPin.project extra34 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc34w107 stored19 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xffffeeeeffffeeeeffffaaaaffffaaaaffffeeeeffffeeeeffffaaaaffffaaaa : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w109 pc26w48 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w109 stored3 rfl rfl
private theorem pc30w112 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w111 : PetersenPackedPin.project extra30 (0xfffffcfcfffffcfcfffff0f0fffff0f0fffffcfcfffffcfcfffff0f0fffff0f0 : BitVec 256) = 0xfffffffffffffffff000f000f000f000 := PetersenWireProjection.derive 3 pc30w112 pc30w55 rfl rfl
private theorem pc30w113 : PetersenPackedPin.project extra30 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff000f000f000f000 := PetersenWireProjection.derive 3 pc30w112 stored11 rfl rfl
private theorem pc32w115 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl
private theorem pc32w114 : PetersenPackedPin.project extra32 (0xffffffccffffffccffffff00ffffff00ffffffccffffffccffffff00ffffff00 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc32w115 pc32w63 rfl rfl
private theorem pc32w116 : PetersenPackedPin.project extra32 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc32w115 stored27 rfl rfl
private theorem pc3w118 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl
private theorem pc3w117 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w118 stored36 rfl rfl



private theorem pc0w122 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl


private theorem pc0w124 : PetersenPackedPin.project cycle0 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored51 stored52 rfl rfl
private theorem pc0w121 : PetersenPackedPin.project cycle0 (0xffffffffffffccccffffffffffff0000ffffffffffffccccffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 pc0w122 pc0w124 rfl rfl
private theorem pc0w127 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w122 stored52 rfl rfl



theorem b3_3402 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3402 := by
  apply PetersenIndexedNode.close (bank := [a6228,s4_2984,a6229,a6230,s4_1502,a6231,a6232,a5876,a6233,a5688,a6234,a6235,s4_101,a6236,a6237,s4_3003,a6238,a6239,a6240,s4_2985,a6241,a6242,s4_1654,s4_3005,a6243,a6244,a5242,s4_2082,a6245,s4_3011,a6246,a6247,a5691,a6248,a6249,a6250,s4_2968,a6251,s4_2969]) (PetersenIndexedNode.reasons 256 17 420 0x4909400810809000c6222210112424c44449094009a004b00248011c0088840492122141108098889002162224008085044282622210a090889001f800f21111444421011080a4848c282a20251111850544449212108088405c0c021011080b111054142a0a70300a8285414c44410808840600382101108090a08c2826141800e98504c28242821080884052425001b490128888a08092024909141012424a222800d2888a003050402820311112100d040800ca42012100c444282014102002c9080484010a08a0805040800b94100a080428248402420062225040188088404e0c0210118889c18042222101282008405343428204d0924848908092124d0d121012434921214102484a0028282014103111054442a22800a8a8885444c44414100a08191102820141010a08908048406444121009080428214100a080501048401400084045040280014040a0805010210124200840531102820141014100706038204c440e0c05060504014100a08200240602030124849090086028009a120109009212030101809888900116220381800c0406026222018080c04e060800838182001c0602030110a098980c4808007b1301098042820301018084a0a06021280884044c442101128289888420a2101030108404a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092425000d49094003107028381490920e052025000b80052404a001300080180b111107020301214120e048500c888216010a00850442c021413222107028381150520e04541421018003084045415000715050840507022101494120e05250050408002141012505000548411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808001212000c05000303012120107028480800000c080604921230b020c0a0002616030b0248480604030262a2884804240c444018100c098a8a03020181311104240212064c480c080604428230b0185819312616030b010a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c088480424042c0018100c0907020302018110b0042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1594 theta)
    · exact b4_2984 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1654 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_3005 theta)
    · exact b4_1502 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_3003 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_793 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3011 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_779 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_778 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2743 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2729 theta)
    · exact b4_101 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1117 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1502 theta)
    · exact b4_3003 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2366 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2082 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1807 theta)
    · exact b4_2985 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1594 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2984 theta)
    · exact b4_1654 theta
    · exact b4_3005 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1807 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2985 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2366 theta)
    · exact b4_2082 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_793 theta)
    · exact b4_3011 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2743 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2729 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_101 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1117 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_779 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_778 theta)
    · exact b4_2968 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2969 theta)
    · exact b4_2969 theta
theorem b3_3403 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3403 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_3403 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored95 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons pc41w6 (PetersenWireProjection.cons pc41w5 (PetersenWireProjection.cons pc41w0 rfl)))))))))) (by decide +kernel)
theorem b3_3404 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3404 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,true)),(false,(3,true),(1,true))] s3_3404 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w17 (PetersenWireProjection.cons pc26w12 rfl))))))))) (by decide +kernel)
theorem b3_3405 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3405 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(3,true)),(false,(6,true),(3,true))] s3_3405 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w28 (PetersenWireProjection.cons pc30w23 rfl))))))))) (by decide +kernel)
theorem b3_3406 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3406 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,true),(2,true)),(false,(6,true),(4,true))] s3_3406 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffff00ff00ffffffffff00ff00,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons pc30w28 (PetersenWireProjection.cons pc30w34 rfl))))))))) (by decide +kernel)
theorem b3_3407 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3407 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(4,true)),(false,(7,true),(1,true))] s3_3407 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w40 (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons pc34w35 rfl))))))))) (by decide +kernel)
theorem b3_3408 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3408 := by
  apply PetersenIndexedNode.close (bank := [a6252,s4_3012,a6253,a6254,s4_1508,a6255,a6256,a6257,s4_3181,a6258,s4_3020,a6259,a6260,a6261,a6262,a6263,a6264,a6265,a6266,a6267,a6268,a6269,a6270,a6271,s4_3013,a6272,a6273,s4_1808,a6274,a6275,s4_3014,a6276,s4_2089,a6277,a6245,a6278,a6279,a6280,s4_3006,a6281,a6282,s4_3009,a6283,a6284,a6285]) (PetersenIndexedNode.reasons 256 17 420 0x4909400b1080870306222210112424c44449091c0c2005670303111400a884049212214110808c444428231112484a005292126222400a188890027214110a098888428242224009a004a8444311140090c444921230a0a4848c444614121112484a004692125030185054080c44450602810140c0a0c0503031110c28261418011400844202428230a08840524250020490118888a080920249091410124246222800f9888a003a50402820311112100d040800f242012100c44428201410200369080484010a08a0805040800e14100a080428248402420200325040282018504e0c07040800d1c180a0c06141282014101343428204d0924848908092124d0d121012434921214102484a002e282014103111054442a22800c0a8885444c44414100a08191110016644010a085040282064440a08050404282800a90a0a0026484024201850450402820800a0a0805040614124201210131102820141014100706038204c440e0c05060504014100a080e8680602030124849090086023a1a21200e0689212030101809888900126220281800c0406026222018080c04a0608008a8182001e0602030110a084c4426228008098884c444282030101808ca8a06020301185044c44262232a2898884c446141030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018092425000e49091c0c107027030490920e05202470308006a404a0019000b0180b111107020301214120e048500c888216010a00850442c0214132221070283818003a0e05070261418003185060015000980041850507026141494120e05250050408002141012505000548411410107025040151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808001212000c05000303012120107028480800000c080604921230b020c0a0002616010b0248480604030262a2884804240c444018100c098a8a03020181311104240212064c480c080604428210900848193122120109010a080604030230a080c080604a0c0109008480c28221201090283000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c088480424042c0018100c0907020302018110b0042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1598 theta)
    · exact b4_3012 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1665 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_3022 theta)
    · exact b4_1508 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_3021 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_799 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_799 theta)
    · exact b4_3181 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3020 theta)
    · exact b4_3020 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_794 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_793 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2747 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1122 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1595 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3013 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2367 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2093 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1665 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3022 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2367 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2093 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1595 theta)
    · exact b4_3013 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1508 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_3021 theta)
    · exact b4_1808 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3014 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1808 theta)
    · exact b4_3014 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2372 theta)
    · exact b4_2089 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_794 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_793 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2747 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1122 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3006 theta)
    · exact b4_3006 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_158 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_158 theta)
    · exact b4_3009 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_123 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3009 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_123 theta)
theorem b3_3409 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3409 := by
  apply PetersenIndexedNode.close (bank := [s4_2473,s4_53,a6286,s4_3023,a6287,s4_3029,a6288,s4_105,a6289,s4_3024,a6290,s4_3032,a6291,s4_132,a6292,s4_3025,a6293,s4_3030,a6294,a6295,a6296,s4_3026,s4_1655,s4_3033,a6297,s4_3031,a5345,a5346,a6298,s4_149,s4_2063,s4_2064,s4_2012,s4_3027,a6299,s4_3034,a6300,a6301,a6302,s4_3028,a6303,a6304,a6305,a6306,s4_5,a6307,a6308]) (PetersenIndexedNode.reasons 256 17 417 0x1002e80152480a0058c4444901400b600565202801630a08a404c4448015b11120054c2826141400a6005084448013084044203002530a098506004e614130a0c0090420221017030084044202c444504038101c0c0a080703031110420221018011084044202c28230a0985060046614130a0b0a084202210180104007e003d001d282014102004250402820400720037001a800c14100a080c44448403410200329080484031110a0805040800b242012100c282282014102002e5040282030a09210090801505141006202210138300840454147060150508404a0802101800a0a08050410013242012102002a48402420400485040282080080a0805040c4446460321020022c8c02460311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a00050102820140408404908021014c440a0805040504015110e08131102a22151114100504028208007018080c05000d424021202001e84804240400300c0406026222018080c04e060424031101888884806222381800c0406028005018080c04c2826260312020016c4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421012a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602800400c44062300072120109020012424021204001806220311800200c440622c44441c0b0902000a838141c0b111006220311614100c440622c8882120109018504424021203222006220311150500c4454142101131a08404541426341505084040622210149411090006025040018880c052504031101889410084804240151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311800100c080605000130b0185820006616030b0400000604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2473 theta
    · exact b4_53 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1599 theta)
    · exact b4_3023 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_816 theta)
    · exact b4_3029 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2732 theta)
    · exact b4_105 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1124 theta)
    · exact b4_3024 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1514 theta)
    · exact b4_3032 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2450 theta)
    · exact b4_132 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1812 theta)
    · exact b4_3025 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1513 theta)
    · exact b4_3030 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2451 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_133 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1811 theta)
    · exact b4_3026 theta
    · exact b4_1655 theta
    · exact b4_3033 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1656 theta)
    · exact b4_3031 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2357 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2354 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2352 theta)
    · exact b4_149 theta
    · exact b4_2063 theta
    · exact b4_2064 theta
    · exact b4_2012 theta
    · exact b4_3027 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_815 theta)
    · exact b4_3034 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2733 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_106 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1123 theta)
    · exact b4_3028 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2759 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2760 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_715 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_713 theta)
    · exact b4_5 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_712 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_714 theta)
theorem b3_3410 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3410 := by
  apply PetersenIndexedNode.close (bank := [a6309,s4_3042,a6310,s4_183,a6311,s4_3036,s4_2774,s4_207,a6312,s4_3037,a6313,s4_3044,a6314,a6315,a6316,s4_3038,a6317,s4_3043,a6318,a6319,a6320,s4_3039,a6321,s4_3045,a6322,a6323,a6324,s4_3040,a6325,a6326,s4_979,a6327,s4_6,a6328,a6329,a6330,a6331,s4_3041,s4_978]) (PetersenIndexedNode.reasons 256 17 417 0x10026800f2480a0040a02049014009084044202801198888c445002531111888a0044420221013818084044202501030a094040e06061412818140404202210140086003e21018010282004202a020800fa8082003ca08050404007600388424311128200c4444202706010808c444e0c031111080941004202800d14100a081001938301c18200367060383040060a08050405818141016040a02048402808160609080501828080a080a020210124200a00048082820140008404504021011202121004808800b14100a080a08038301c182002e7060383028200a0805040800a121009081001314100a082002a28201410400489080484080080a0805040a0206460280820022c8c06460280805040282024040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028208007018080c05000d13110988a001e26221311400300c0406025212018080c04a020424028081484884805012280800c0406022606018080c0442026260108089818c4c02406108080c0406028005018080c04a08013110988a001626221311282000c0406022a22098884c445040030101808a88806020301141004c4426221612018080c04282007050380858480e0a03050a0800c040602800400c44062300071312098920012262413124001806220311511100c440622a02041c0a80814444838150112808006220311210100c44840448083130120208404626021011202006225002514100c440622a080131209891450426241312282000622031149410989006025040018880c05250403110188941004c482624151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311800200c0806050003109008482000a212010904000806040302800000c080604a02041c1280820002838241c12808006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b4_1521 theta)
    · exact b4_3042 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2425 theta)
    · exact b4_183 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1782 theta)
    · exact b4_3036 theta
    · exact b4_2774 theta
    · exact b4_207 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1173 theta)
    · exact b4_3037 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1510 theta)
    · exact b4_3044 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2431 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_186 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1774 theta)
    · exact b4_3038 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1516 theta)
    · exact b4_3043 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2428 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_189 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1777 theta)
    · exact b4_3039 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1509 theta)
    · exact b4_3045 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2436 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_220 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1773 theta)
    · exact b4_3040 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2684 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2673 theta)
    · exact b4_979 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_993 theta)
    · exact b4_6 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_992 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2777 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_211 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1170 theta)
    · exact b4_3041 theta
    · exact b4_978 theta
theorem b3_3411 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3411 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_3411 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons pc26w46 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3412 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3412 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,true))] s3_3412 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3413 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3413 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true))] s3_3413 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w56 (PetersenWireProjection.cons pc30w53 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3414 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3414 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3414 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w66 (PetersenWireProjection.cons pc32w60 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_3415 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3415 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3415 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_3416 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3416 := by
  apply PetersenIndexedNode.close (bank := [a6332,s4_3106,a6333,a6334,a6335,s4_3053,a6336,s4_3160,s4_2663,a6337,a6338,s4_3054,a6339,a6340,a6341,s4_3055,a6342,a6343,a6344,a6345,a6346,s4_3056,a6347,a6348,a6349,a6350,s4_7,a6351,a6352,s4_1615,s4_900,a6353,a6354,a6355,s4_3099,s4_984,s4_3100,a6356,a6357,a4920,s4_3067,a6358,s4_1131,a6359,s4_3077]) (PetersenIndexedNode.reasons 256 17 417 0xc4442101108092404c28249013111185048444490110808840492028015a48090809002a42022480a005892024202400a5080842028013908089011002624041080a005042022404400949010a02015052c809240500234901280820048a02049010a829240462221505188088405002121011888a0044422221010a82884050020800c0840600342a0a1080a4808e0c0920242024007908089202800fa48090808706042021080a003a420224041c180901042023830108089011001c24044006e00325040800d1c180a0802a0a800c8a82a0030706038304005e002c21114d050a081340492026460248093414c8c04905248085040920224040a080900042022420120009010484024041080850404202800a121009081001314100a082002a2820141040048908048401505121005404311114100a8085414282015050c4449080311180080a0805040706015110e08200222a2215111c1805040282042020180908009202424021001080884804202248080c0406022606018080c0442026260108089818c4c02406108080c0406028007212010901000d03010180a001e0602030140031090084801a8a818080c042a0a1311098086a2a2622188a8a8280c0406023a3221200e8c07060030101808e8c8060203011c181090070601612018080c04282007050380858480e0a03050a0800c040602490100c450602840441c0a0c052404838148012101006229002210100c44840448086160120208404c2c021011202006225002800520e0507030009018880c46001603110188c002107028381150500c4454143111131a08c445414263415050c4440622380a800320e044c487060018880c46000e031101889c18107027060151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311428280c080604920241c1248090a0a83824202a480806040302248480c080604420230b0108089212616024049080806040302800220e0907050003018100c0a000a030201814000907048382188880c0806042a0a109008c086222212018888a8280604030280000848042407060018100c0a0002030201811c1804240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1393 theta)
    · exact b4_3106 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2342 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_310 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1759 theta)
    · exact b4_3053 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_473 theta)
    · exact b4_3160 theta
    · exact b4_2663 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_290 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_891 theta)
    · exact b4_3054 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2442 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_288 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1574 theta)
    · exact b4_3055 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1569 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3163 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2337 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_312 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1790 theta)
    · exact b4_3056 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2592 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2593 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_480 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1423 theta)
    · exact b4_7 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1420 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2324 theta)
    · exact b4_1615 theta
    · exact b4_900 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_3164 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_479 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_803 theta)
    · exact b4_3099 theta
    · exact b4_984 theta
    · exact b4_3100 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2659 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_901 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_329 theta)
    · exact b4_3067 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2708 theta)
    · exact b4_1131 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_323 theta)
    · exact b4_3077 theta
theorem b3_3417 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3417 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_3417 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3418 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3418 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3418 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_3419 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3419 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(5,true)),(false,(0,true),(7,true))] s3_3419 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff00000000ff00ff00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w56 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3420 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3420 := by
  apply PetersenIndexedNode.close (bank := [s4_2445,a6360,a6361,s4_3058,a6362,s4_3161,a6363,a6364,a6365,s4_3059,a6366,a6367,a6368,s4_3060,a6369,a6370,a6371,a6372,a6373,s4_3061,a6374,a6375,a6376,s4_1616,s4_7,s4_1612,a6377,a6378,a6379,s4_3067,a6380,a6381,s4_3094,a6382,a6383,a6384,s4_3083]) (PetersenIndexedNode.reasons 256 17 417 0x92028011a48090809002242022480a004892024202400850808c4442101108092405001f4901311120040c4444901108088405001e800b12022003042022101280804202a0004901282014000a020504028081240421011080c007042022101800d8a8285415001d15050a82a00342101108098888420221012101185048404622230a090888840421011080a4808a08092024202343010808920268602480908085040420240066002e9080800c14100a0804202800b9080a002c5040282040056002848181505141005414210138300840454147060150508404a08021014d050a081340492026460248093414c8c04905248085040920280090a0805041001115110a88a00262a221511400405040282025050a0809404420224201080894144840210510808504042021404121005000210114100a000501028201404084049080210180070a0805040504015110a88a001e2a221511141005040282042020180908009202424021001080884804202248080c0406028006212010901000b03010180a001a0602030140029090084802a0a018080c044202626010808a828c4c0280a108080c0406021282818084a0221011311084044a0a26221082884040c0421012a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602490100c450602840441c0a0c052404838148012101006229002800420e0507030007018880c46001203110188c001907028381210100c44840450106160108408404c2c021011404006225002150500c4454142101131a084045414263415050840406222101800220e0484805040018880c46000a031101889410107025040151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311428280c080604920241c1248090a0a83824202a48080604030280010848042410001018100c0a0006030201814000042402120288880c080604420230b010808a222616028089080806040302108080c08420028081090084004202212010808a0200604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2445 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_228 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1547 theta)
    · exact b4_3058 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_472 theta)
    · exact b4_3161 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2710 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_242 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1011 theta)
    · exact b4_3059 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2443 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_240 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1571 theta)
    · exact b4_3060 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1570 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3166 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2335 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_239 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1791 theta)
    · exact b4_3061 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2323 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2321 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_888 theta)
    · exact b4_1616 theta
    · exact b4_7 theta
    · exact b4_1612 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2661 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_230 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_848 theta)
    · exact b4_3067 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_887 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_807 theta)
    · exact b4_3094 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2770 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1176 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_265 theta)
    · exact b4_3083 theta
theorem b3_3421 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3421 := by
  apply PetersenIndexedNode.close (bank := [a6385,s4_3091,s4_2448,a6386,a6387,s4_3063,a6388,s4_3096,s4_2730,a6389,a6390,s4_3064,a6391,a6392,a6393,s4_3065,a6394,s4_3098,a6395,s4_3093,a6396,a6397,a6398,a6399,a4186,a6400,a6401,s4_3066,a6402,s4_3099,a6403,a6404,a6405,a6406,a6407,s4_3067,a6408,a6409,a6410,a6411,s4_7,a6412,a6413,a6414,s4_3095,a6415,a6416,a6417,s4_3084]) (PetersenIndexedNode.reasons 256 17 417 0xa0208017a80812405002e4901280820060a0204901400b52404c4443111380812405002b4901311120058c4444901188892405002a80131080a00506222210128080c282a0204901383012404a020706028081240461414901400a6004e21018014185044202622280139888a004c614130a0c0096004842224901141012000840448402400124049080490121010a0808404801124201210100212820141020046504028204008121009080311124200e041001f28201c080c444504031114007921009080800e14100a080614138301c102003a7060283018504a08050404d050a081340492026460248093414c8c049052480850409202800d400660031001714100a0820036282014104005a002b001480090a0805040622224201a08200264840242018888504028208008121009080614114100a08200222820141018504908048404c440a0805040504015110e08131102a221511141005040282042020180908009202424021001080884804202248080c0406028007018080c05000d13110988a001e26221311400300c0406023a1a018080c046222626018888e868c4c0381a188880c04060232a2818080c046141131109888ca8a26221311185040c0406022a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602490100c450602840441c0a0c052404838148012101006229002800500c4406230009131a098d200162634131a4002006220311311100c44062270306160188c0c444c2c031111c0c006220311800300c4406226141131a098d2000e2634131a1850406220311494120e0406025040018880c052504031101889410107025040151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311428280c080604920241c1248090a0a83824202a480806040302800200c0806050003109008482000a212010904000806040302800000c080604622230b0184820002616010b0188880604030230a080c080604e0c0109008480c28221201090383000604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1522 theta)
    · exact b4_3091 theta
    · exact b4_2448 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_137 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1816 theta)
    · exact b4_3063 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_805 theta)
    · exact b4_3096 theta
    · exact b4_2730 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_112 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1104 theta)
    · exact b4_3064 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2476 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_56 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1596 theta)
    · exact b4_3065 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1663 theta)
    · exact b4_3098 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1661 theta)
    · exact b4_3093 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2369 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2368 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2350 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_146 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2098 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2099 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2097 theta)
    · exact b4_3066 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1426 theta)
    · exact b4_3099 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2322 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_889 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2866 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_140 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1673 theta)
    · exact b4_3067 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2620 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2617 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_708 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_820 theta)
    · exact b4_7 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_819 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_707 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_809 theta)
    · exact b4_3095 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2787 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1106 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_116 theta)
    · exact b4_3084 theta
theorem b3_3422 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3422 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(2,true))] s3_3422 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcfcfcccccfcfcccccfcfcccccfcfcccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w49 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w81 rfl))))))))) (by decide +kernel)
theorem b3_3423 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3423 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3423 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w74 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w82 rfl))))))))) (by decide +kernel)
theorem b3_3424 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3424 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(0,false),(2,true)),(false,(0,true),(4,true))] s3_3424 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff0aff0aff0aff0aff0aff0aff0aff0a,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w66 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w83 rfl))))))))) (by decide +kernel)
theorem b3_3425 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3425 := by
  apply PetersenIndexedNode.close (bank := [a6418,a6419,a6420,s4_3068,s4_7,a6421,a6422,a6423,a6424,s4_3165,a6425,a6426,a6427,a6428,a6429,a6430,a6431,s4_3069,a6432,a6433,a6434,s4_3070,a6435,a6353,a6436,a6437,s4_899,a6438,a6439,a6440,a4462,a6441,s4_3077,a6442,s4_3089,a6443,a4924,a6444,s4_3083,s4_898]) (PetersenIndexedNode.reasons 256 17 411 0x4009e00348404800224809240500252404120220048420221014009884044202801192020901100212101108092404c2824901400898504c2824901108088405001f108088406003c2a0a15054008054142a0a800e884044202b2221080884052404a08049012c889410092224901084044202622210808840484046141308098888c28242222101084044203001c800d941020008908028202480a00369202800d2420121010019800c2105084049080210112021a18048082101343008404480848401202054149080150508406002c210115054005c541421014840084060028282014104004c54442a22800a8a8885445001214100a081341428204d0124809918092024d053230124149202141024808901028202400108089080480024041210090104202141010808501048401400084045040280014040a080501021012420084053110282014102420054442a224c440a8885444908014100a0820021000f8007400340c0406028008818080c05000c8005c002928280602030124809090092024a0a21201202892020301018089818060203011080989804202260631300901842020301018084a0a06021280884044c442101128289888420a2101030108406001084804240242000c0406028004818080c0490804240212005848060203010a0801c140e021612038280c14282003010180a000f00068002c001006220311490100c452404901041c0a40412404838148012404006229002210100c44840448086160120208404c2c021011202006225002150500c4454142101131a084045414263415050840406222101494120e0525009080018880c45250403110188a420107029080151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c0406140301212000622031180010848042410001018100c0a0006030201814000042402120488880c080604920241c124809222283824808a480806040302248480c080604420230b0108089212616024049080806040302108080c08420028081090084004202212010808a0200604030248c08848042409080018100c09230203020181242004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym1 fix1 (by decide +kernel) (b4_2472 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_31 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1820 theta)
    · exact b4_3068 theta
    · exact b4_7 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_844 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_846 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_845 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1567 theta)
    · exact b4_3165 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2381 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2380 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2379 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_32 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2240 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2241 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2239 theta)
    · exact b4_3069 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2482 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_27 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1604 theta)
    · exact b4_3070 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_481 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3164 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2267 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_2265 theta)
    · exact b4_899 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1660 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1657 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2757 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_29 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1130 theta)
    · exact b4_3077 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_810 theta)
    · exact b4_3089 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2789 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_39 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1129 theta)
    · exact b4_3083 theta
    · exact b4_898 theta
theorem b3_3426 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3426 := by
  apply PetersenIndexedNode.close (bank := [a6445,s4_3085,a6446,s4_184,a6447,s4_3073,s4_2775,s4_208,a6448,s4_3074,a6449,s4_3097,a6450,a6451,a6452,s4_3075,a6453,s4_3087,a6454,a6455,a6456,s4_3076,a6457,s4_3100,a6458,a6459,a6460,s4_3077,a6461,a6462,s4_982,a6463,s4_7,a6464,a6465,a6466,a6467,s4_3084,s4_981]) (PetersenIndexedNode.reasons 256 17 417 0x10026800f2480a0040a02049014009084044202801198888c445002531111888a0044420221013818084044202501030a094040e06061412818140404202210140086003e21018010282004202a020800fa8082003ca08050404007600389222311128200c4444202706010808c444e0c031111080941004202800d14100a081001938301c18200367060383040060a08050405911141016040a02048402808164449080511128080a080a020210124200a00048082820140008404504021011202121004808800b14100a080a08038301c182002e7060383028200a0805040800a121009081001314100a082002a28201410400489080484080080a0805040a0206460280820022c8c06460280805040282024040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a0805040504015110e08131102a22151114100504028208007018080c05000d13110988a001e26221311400300c0406025212018080c04a020424028081484884805012280800c0406022606018080c0442026260108089818c4c02406108080c0406028005018080c04a08013110988a001626221311282000c0406022a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602800400c4406230007131a098d200122634131a4001806220311591100c440622a02041c0a80816444838158112808006220311210100c44840448086160120208404c2c021011202006225002514100c440622a080131a098d145042634131a2820006220311494120e0406025040018880c052504031101889410107025040151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311800200c0806050003109008482000a212010904000806040302800000c080604a02041c1280820002838241c12808006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b4_1523 theta)
    · exact b4_3085 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2426 theta)
    · exact b4_184 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1783 theta)
    · exact b4_3073 theta
    · exact b4_2775 theta
    · exact b4_208 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1174 theta)
    · exact b4_3074 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1511 theta)
    · exact b4_3097 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2432 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_187 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1775 theta)
    · exact b4_3075 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1517 theta)
    · exact b4_3087 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2429 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_190 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1778 theta)
    · exact b4_3076 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1425 theta)
    · exact b4_3100 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2870 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_221 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1671 theta)
    · exact b4_3077 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2685 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2675 theta)
    · exact b4_982 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_995 theta)
    · exact b4_7 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_994 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2778 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_212 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1171 theta)
    · exact b4_3084 theta
    · exact b4_981 theta
theorem b3_3427 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3427 := by
  apply PetersenIndexedNode.close (bank := [s4_2474,s4_54,a6468,s4_3079,a6469,s4_3086,a6470,s4_107,a6471,s4_3080,a6472,s4_3092,a6473,s4_134,a6474,s4_3081,a6475,s4_3088,a6476,a6477,a6478,s4_3082,s4_1613,s4_3094,a6479,s4_3089,a6480,a6481,a6482,s4_150,a4162,a6483,a6484,s4_3083,a6485,s4_3095,a6486,a4466,a6487,s4_3084,a6488,a6489,a6490,a6491,s4_7,a6492,a6493]) (PetersenIndexedNode.reasons 256 17 417 0x1002e80152480a0058c4444901400b600564202801630a088404c4448015b11120054c2826141400a6005084448013084044203002530a098506004e614130a0c0090420221017030084044202c444504038101c0c0a080703031110420221018011084044202c28230a0985060046614130a0b0a084202210180104007e003d001d282014102004250402820400720037001a800c14100a080c44448403410200329080484031110a0805040800b242012100c282282014102002e5040282030a09210090801505141006202210138300840454147060150508404a0802101800a0a08050410013242012102002a48402420400485040282080080a0805040c4446460321020022c8c02460311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a00050102820140408404908021014c440a0805040504015110e08131102a22151114100504028208007018080c05000d424021202001e84804240400300c0406026222018080c04e060424031101888884806222381800c0406028005018080c04c2826260312020016c4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421012a2221200a8805040030101808a8880602030114101090050401612018080c04282007050380858480e0a03050a0800c040602800400c440623000741c0a0e060012838141c0c001806220311800200c440622c44441c0b0902000a838141c0b111006220311614100c440622c888616030a018504c2c061413222006220311150500c4454142101131a084045414263415050840406222101494120e0406025040018880c052504031101889410107025040151100c4406222820058c82c4454440b19018c8a08006220311030100c440c048480030a018400c04061403012120006220311800100c080605000130b0185820006616030b0400000604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a08848042405040018100c08a28203020181141004240212024a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201888848006200614018100c080622030201810185042400614)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2474 theta
    · exact b4_54 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1600 theta)
    · exact b4_3079 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_825 theta)
    · exact b4_3086 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2735 theta)
    · exact b4_107 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1126 theta)
    · exact b4_3080 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1515 theta)
    · exact b4_3092 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2453 theta)
    · exact b4_134 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1813 theta)
    · exact b4_3081 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1518 theta)
    · exact b4_3088 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2452 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_135 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1814 theta)
    · exact b4_3082 theta
    · exact b4_1613 theta
    · exact b4_3094 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1658 theta)
    · exact b4_3089 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2868 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2869 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2867 theta)
    · exact b4_150 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1737 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1744 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1715 theta)
    · exact b4_3083 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_824 theta)
    · exact b4_3095 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2734 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_108 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1125 theta)
    · exact b4_3084 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2763 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2762 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_719 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_723 theta)
    · exact b4_7 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_722 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_718 theta)
theorem b3_3428 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3428 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s3_3428 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w84 (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3429 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3429 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_3429 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3430 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3430 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(0,true),(7,true))] s3_3430 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons pc30w89 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3431 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3431 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3431 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xaaaaaaaa,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w97 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons pc2w94 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_3432 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3432 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false)),(false,(0,true),(2,true))] s3_3432 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffccccffffcccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w13 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3433 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3433 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3433 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w103 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons pc3w80 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_3434 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3434 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false)),(false,(0,true),(7,true))] s3_3434 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffaa00aa00aa00aa00,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w91 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w24 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3435 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3435 := by
  apply PetersenIndexedNode.close (bank := [s4_2446,a6494,a6495,s4_3116,a6496,s4_3162,s4_2758,a6497,a6498,s4_3115,a6499,a6500,a6501,s4_3117,a6502,a6503,a6504,a6505,a6506,s4_3118,a6507,a6508,a6509,a6510,s4_8,a6511,a6512,a6513,a6514,s4_3119,a6515,a6516,a6517,a6518,a6519,a6520,s4_3124]) (PetersenIndexedNode.reasons 256 17 417 0x90108011a404108090022420224042004890104202400850808c4442808140410809001f4202311120040c4444202140410809001e800b1080a003050102101280804202a0004202282014000a020504028081080821011080c007042022101800d8c4446223001d18888c4460034210110809888842022101280818504a020622230a094888a02021011080a4040a08090104202343010808901068602404108085040420240066002e9080800c14100a0805010800b94042002c5040282040056002842121888941006222210138300840462227060188888404a080210146060a081180884046460210111818c8c04206210105040840480090a0805041001115110a88a00262a22151140040504028202c0c0a080b0205010242014040b0304840280c14040504050101404121005000210114100a000501028201404084049080210180070a0805040504015110a88a001e2a221511141005040282042020180908009010424021001080884804202240400c0406028006018080c05000b0b090584a001a16120b09400280c0406022a0a018080c045010626014040a828c4c0280a140400c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905848a88816120b09141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301800400c0406030007098884c46001213110988c001806020301290900c0406025010212014040a424424028091404006020301150d00c0406022101131a084045434263414050840406020301800200c0406025040098884c46000a131109889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302800100c0806050001098904c4a0006131209894000006040302288880c080604501030b014040a222616028089404006040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c48a28213120989141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2446 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_166 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1789 theta)
    · exact b4_3116 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_474 theta)
    · exact b4_3162 theta
    · exact b4_2758 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_30 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1012 theta)
    · exact b4_3115 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2444 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_164 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1603 theta)
    · exact b4_3117 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1573 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3167 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2378 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_167 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1792 theta)
    · exact b4_3118 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2655 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2656 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_896 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1234 theta)
    · exact b4_8 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1233 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2786 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_160 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_847 theta)
    · exact b4_3119 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_895 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_814 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3127 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2785 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1128 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_165 theta)
    · exact b4_3124 theta
theorem b3_3436 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3436 := by
  intro m le c
  apply rejects_sound cycle2 i5 6 tgt small2 hot2 [] s3_3436 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored48 (PetersenWireProjection.cons stored47 (PetersenWireProjection.cons stored46 (PetersenWireProjection.cons stored45 (PetersenWireProjection.cons pc2w97 (PetersenWireProjection.cons stored43 (PetersenWireProjection.cons stored42 (PetersenWireProjection.cons pc2w105 (PetersenWireProjection.cons stored41 rfl))))))))) (by decide +kernel)
theorem b3_3437 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3437 := by
  apply PetersenIndexedNode.close (bank := [s4_2475,s4_55,a6521,s4_3121,a6522,s4_3125,a6523,s4_109,a6524,s4_3122,a6525,a6526,a6527,s4_136,a6528,s4_3123,a6529,s4_3126,a6530,a6531,a6532,a6533,a6534,a6517,a6535,s4_3127,s4_3108,s4_3109,s4_3107,s4_148,a5014,a6536,a6537,s4_3124,a6538,a6539,a6540,a6541,a6542,a6543,a6544,a6545,a6546,a6547,s4_8,a6548,a6549]) (PetersenIndexedNode.reasons 256 17 417 0x1002e8015210120058c4444202400b600564202801630a088404c4448015b11120054c2826141400a6005084448013084044203002530a098506004e614130a0c0090420221017030084044202c444504038101c0c0a080703031110420221018011084044202c28230a0985060046614130a0b0a084202210180104007e003d001d282014102004250402820400720037001a800c14100a080c44448403410200329080484031110a0805040800b242012100c282282014102002e5040282030a09210090801888941006202210138300840462227060108888404a0802101800a0a08050410013242012102002a48402420400485040282080080a0805040c4446460321020022c8c02460311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a00050102820140408404908021014c440a0805040504015110e08131102a22151114100504028208007018080c05000d424021202001e84804240400300c0406026222018080c04e060424031101888884806222381800c0406028005018080c04c2826260312020016c4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800400c04060300072120109020012424021204001806020301800200c040602c44441c0b0902000a838141c0b111006020301614100c040602c8882120109018504424021203222006020301150d00c0406022101131a084045434263414050840406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800100c080605000130b0185820006616030b0400000604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_2475 theta
    · exact b4_55 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1601 theta)
    · exact b4_3121 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_828 theta)
    · exact b4_3125 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2736 theta)
    · exact b4_109 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1127 theta)
    · exact b4_3122 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1519 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3126 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2454 theta)
    · exact b4_136 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1815 theta)
    · exact b4_3123 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1519 theta)
    · exact b4_3126 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2454 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_136 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1815 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3123 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1237 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3127 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1237 theta)
    · exact b4_3127 theta
    · exact b4_3108 theta
    · exact b4_3109 theta
    · exact b4_3107 theta
    · exact b4_148 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1248 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1245 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1247 theta)
    · exact b4_3124 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_828 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3125 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2736 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_109 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1127 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3122 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2765 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2765 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_726 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_726 theta)
    · exact b4_8 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_725 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_725 theta)
theorem b3_3438 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3438 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s3_3438 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w106 (PetersenWireProjection.cons pc34w50 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3439 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3439 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s3_3439 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons pc26w108 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3440 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3440 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(7,true),(0,true))] s3_3440 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffff000f000f000f000,0xfffffffffffffffff000f000f000f000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w113 (PetersenWireProjection.cons pc30w111 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3441 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3441 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,false)),(false,(4,true),(0,true))] s3_3441 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w116 (PetersenWireProjection.cons pc32w114 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl))))))))) (by decide +kernel)
theorem b3_3442 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3442 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3442 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w117 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w71 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_3443 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3443 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3443 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0xffff0000,0x0,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w127 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons pc0w121 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
end Orbits1020Cost12
