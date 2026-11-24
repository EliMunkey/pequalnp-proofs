import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S0
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S10
import Q1020K12L4S11
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S20
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S27
import Q1020K12L4S28
import Q1020K12L4S32
import Q1020K12L4S33
import Q1020K12L4S34
import Q1020K12L4S35
import Q1020K12L4S37
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S44
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S48
import Q1020K12L4S49
import Q1020K12L4S50
import Q1020K12L4S51
import Q1020K12L4S52
import Q1020K12L4S53
import Q1020K12L4S56
import Q1020K12L4S58
import Q1020K12L4S68
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc30w1 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl

private theorem pc30w0 : PetersenPackedPin.project extra30 (0xfffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xfffffffff0f0f0f0fffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w1 stored8 rfl rfl





private theorem pc30w10 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffff00000000 := PetersenWireProjection.derive 1 stored8 stored11 rfl rfl
private theorem pc30w12 : PetersenPackedPin.project extra30 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored9 stored11 rfl rfl
private theorem pc30w9 : PetersenPackedPin.project extra30 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xfffffffff0f0f0f0 := PetersenWireProjection.derive 3 pc30w10 pc30w12 rfl rfl


private theorem pc32w13 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored24 stored25 rfl rfl

private theorem pc32w16 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl





private theorem pc32w23 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored24 stored27 rfl rfl
private theorem pc32w25 : PetersenPackedPin.project extra32 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xff000000ff000000ff000000ff0000 := PetersenWireProjection.derive 1 stored25 stored27 rfl rfl
private theorem pc32w22 : PetersenPackedPin.project extra32 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000000000000000 : BitVec 256) = 0xff00f000ff00f000ff00f000ff00f0 := PetersenWireProjection.derive 3 pc32w23 pc32w25 rfl rfl



private theorem pc34w27 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl





private theorem pc34w36 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w27 stored19 rfl rfl
private theorem pc34w37 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc34w35 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w36 pc34w37 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w39 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl
private theorem pc34w40 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc34w27 stored16 rfl rfl


private theorem pc29w42 : PetersenPackedPin.project extra29 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored155 stored154 rfl rfl

private theorem pc29w41 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w42 stored153 rfl rfl





private theorem pc29w51 : PetersenPackedPin.project extra29 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 1 pc29w42 stored157 rfl rfl
private theorem pc29w53 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f0 := PetersenWireProjection.derive 1 stored153 stored157 rfl rfl
private theorem pc29w50 : PetersenPackedPin.project extra29 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff := PetersenWireProjection.derive 3 pc29w51 pc29w53 rfl rfl
private theorem pc29w54 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl


private theorem pc39w56 : PetersenPackedPin.project extra39 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored74 stored79 rfl rfl

private theorem pc39w55 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc39w56 stored73 rfl rfl
private theorem pc39w60 : PetersenPackedPin.project extra39 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored73 stored74 rfl rfl





private theorem pc39w66 : PetersenPackedPin.project extra39 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc39w56 stored76 rfl rfl
private theorem pc39w68 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored73 stored76 rfl rfl
private theorem pc39w65 : PetersenPackedPin.project extra39 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 pc39w66 pc39w68 rfl rfl


private theorem pc26w71 : PetersenPackedPin.project extra26 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored0 stored1 rfl rfl






private theorem pc26w79 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0x8888888800000000888888880000000088888888000000008888888800000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w79 stored2 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0x8888888888888888000000000000000088888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w79 stored1 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w85 : PetersenPackedPin.project extra26 (0x8888888888888888888888880000000088888888888888888888888800000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w84 pc26w79 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored1 stored2 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888800000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w79 stored0 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888000000008888888800000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w83 pc26w79 rfl rfl
private theorem pc26w89 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888880000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w80 pc26w79 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0 := PetersenWireProjection.derive 1 stored0 stored6 rfl rfl
private theorem pc26w92 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w90 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffff0f0fffff0f0fffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w91 pc26w92 rfl rfl
private theorem pc26w94 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w93 : PetersenPackedPin.project extra26 (0xccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffff0a0affff0a0affff0a0affff0a0a := PetersenWireProjection.derive 2 pc26w91 pc26w94 rfl rfl
private theorem pc26w96 : PetersenPackedPin.project extra26 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa := PetersenWireProjection.derive 1 stored1 stored6 rfl rfl
private theorem pc26w95 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffccccccccccccccccccccccccffffffffcccccccc : BitVec 256) = 0xffff5555ffff5555ffff0000ffff0000 := PetersenWireProjection.derive 2 pc26w96 pc26w92 rfl rfl
private theorem pc26w98 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored0 stored6 rfl rfl
private theorem pc26w97 : PetersenPackedPin.project extra26 (0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffff5050ffff5050ffff5050ffff5050 := PetersenWireProjection.derive 1 pc26w98 pc26w96 rfl rfl
private theorem pc26w100 : PetersenPackedPin.project extra26 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xffff0000ffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored6 rfl rfl
private theorem pc26w99 : PetersenPackedPin.project extra26 (0xccccccccffffffffccccccccccccccccccccccccffffffffcccccccccccccccc : BitVec 256) = 0xffff0000ffff0000ffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc26w94 pc26w100 rfl rfl
private theorem pc26w101 : PetersenPackedPin.project extra26 (0xccccccccffffffffccccccccffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffff0000ffff0000fffff0f0fffff0f0 := PetersenWireProjection.derive 1 pc26w98 pc26w100 rfl rfl
private theorem pc26w103 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w102 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff0f0f00000f0f0000 := PetersenWireProjection.derive 3 pc26w103 stored2 rfl rfl
private theorem pc26w105 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored2 rfl rfl
private theorem pc26w104 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 2 pc26w105 pc26w84 rfl rfl
private theorem pc26w107 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) = 0x55550000555500005555000055550000 := PetersenWireProjection.derive 2 stored1 stored6 rfl rfl
private theorem pc26w106 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffffccccccccffffffff00000000ffffffffcccccccc : BitVec 256) = 0xffffffffffffffff5555000055550000 := PetersenWireProjection.derive 3 pc26w107 stored2 rfl rfl
private theorem pc26w109 : PetersenPackedPin.project extra26 (0xffffffff000000000000000000000000ffffffff0000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored2 rfl rfl
private theorem pc26w108 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffff5050505050505050 := PetersenWireProjection.derive 1 pc26w83 pc26w109 rfl rfl
private theorem pc26w110 : PetersenPackedPin.project extra26 (0xffffffff33333333ffffffff00000000ffffffff33333333ffffffff00000000 : BitVec 256) = 0xffffffffffffffff0000aaaa0000aaaa := PetersenWireProjection.derive 3 pc26w96 stored2 rfl rfl
private theorem pc26w111 : PetersenPackedPin.project extra26 (0xffffffff33333333ffffffff33333333ffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffff0000f0f00000f0f0 := PetersenWireProjection.derive 3 pc26w91 stored2 rfl rfl
private theorem pc26w112 : PetersenPackedPin.project extra26 (0xffffffffccccccccccccccccccccccccffffffffcccccccccccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffff0000ffff0000 := PetersenWireProjection.derive 0 pc26w94 pc26w92 rfl rfl
private theorem pc26w114 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w113 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffff00000000ffffffffccccccccffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc26w114 stored2 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xfffff0f0fffff0f0ffff0000ffff0000 := PetersenWireProjection.derive 0 pc26w98 pc26w92 rfl rfl
private theorem pc26w117 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w116 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f00000f0f00000 := PetersenWireProjection.derive 3 pc26w117 stored2 rfl rfl
theorem b3_2310 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2310 := by
  apply PetersenIndexedNode.close (bank := [s4_1444,a5217,s4_1,a5218,a5219,s4_2011,s4_1872,a5220,a5221,s4_2066,a5222,a5223,a5224,a5225,s4_1975,s4_1976,s4_1974,a5226,a5227,a5228,a5229,s4_2067,a5230,a5231,a5232,s4_2068,a5233,a5234,a5235,s4_2069,a5236,a5237,s4_1141,s4_1139]) (PetersenIndexedNode.reasons 256 17 408 0x8010c008120010002490124002003f001e280040008a4045000622214808a40492026141248098888c282422224808a4045202800e084044203001b15050a82a003a2a0a15054006842022101591108404420292025040248096444a080491124808420221013911084044202520230a094808e444614129111480842022101800c0a0805041001715110a88a00322a22151140058504028204d050a081340492026460248093414c8c0490524808504092022d050a080b4045202242014808b4144840290514808504052021404121005000210114100a0005010282014040840490802101800a4004e0025001103010180a002a0602030140042001f000e6222018080c049202424024809888884806222248080c0406028006018080c04520262601480a001ac4c04260148080c0406021282818084a0221011311084044a0a26221082884040c0421011612018080c04282007050380858480e0a03050a0800c0406028005c002806030002212000c05240442404901311110702c240490120e052004c444212024008a404838129013222084804240290110900a004c88841c09400854144240150508404c4c02101150518980541421012120084045444424015110a08117122820151122e245444282021200a0800c0442400301212008c8846400301119100c0484802120109020010212010904001c06040302800480c08060500061090084818a8a03020181248090704920262a2a0e09888a9202018100c0993120302018114808c2c0520264c498580c2c05202018100c084202030210800a0204240210010808848042022808018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090109000604030221a080c0806044240109008482000b00048001c0008a08050406222141014444920248402480988889080682024808a080920261412420084045202282010809850450402820148092100520230a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a08006022120141008481000149412420884809282212040000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1444 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_374 theta)
    · exact b4_1 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2872 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2871 theta)
    · exact b4_2011 theta
    · exact b4_1872 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_12 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1828 theta)
    · exact b4_2066 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1071 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1067 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1468 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2086 theta)
    · exact b4_1975 theta
    · exact b4_1976 theta
    · exact b4_1974 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_22 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1845 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1847 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1843 theta)
    · exact b4_2067 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1977 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_14 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1826 theta)
    · exact b4_2068 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1931 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_17 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1177 theta)
    · exact b4_2069 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1054 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1052 theta)
    · exact b4_1141 theta
    · exact b4_1139 theta
theorem b3_2311 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2311 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(5,true)),(false,(7,true),(0,true))] s3_2311 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfffffffff0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xfffffffff0f0f0f0fffffffff0f0f0f0] (PetersenWireProjection.cons pc30w9 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 (PetersenWireProjection.cons pc30w0 rfl))))))))) (by decide +kernel)
theorem b3_2312 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2312 := by
  apply PetersenIndexedNode.close (bank := [s4_1445,a5238,s4_1622,a5239,a5240,a5241,a5242,s4_2010,a5243,s4_2083,a5244,a5245,a5246,a5100,a5247,a5248,s4_1929,s4_1924,s4_75,a5249,a5250,s4_2088,s4_1970,a5251,a5252,s4_2084,a5253,s4_2087,a5254,s4_2089,s4_2031,s4_2030,a5255,a5256,a5257,a5258,s4_2078,s4_2080,s4_2079]) (PetersenIndexedNode.reasons 256 17 414 0x12405002048004004988889000490131111240500268012c0092004700222800248088504500062224008588890020214110a098888428242224007e003c84445911084044202920230a0a480964446141491124808420221017030084044202c44415050a829c0c02a0a15053111042022101800e084044202428230a098506003a614130a090a08420221014d050a081340492022420248093414484049052480850409202800d0a0805040c44415110a88a00362a221511311105040282064440a0805040428224201210191104840242010a08504028201404121005000210114100a0005010282014040840490802101800c018080c04920242402480a003284804240248080c04060262224005d8880e06003010180988880602030138182002ce060800a018080c044282626031202002ac4c0426010a080c0406021282818084a0221011311084044a0a26221082884040c0421011612018080c04282007050380858480e0a03050a0800c04060249014004d2405001241c0a0e0524048381480140046002090028007c00380602c44441c080c048504838121403222085804280214110b008504c88841c0a0e0454148381150508406001821011505400345414210141c0884045444838115110a08117122820151122e245444282041c08a0800c0483810301212020014848003014002c0c04848041c0a120200100302018124808c2c09202800498580c2c09202018100c098a8a21201090311100604030262a280c080604c44410900848193120302018110a08c2c0616064c498580c2c04282018100c084202030210800a0204240210010808848042022808018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c0907022120109010b000604030241c080c08060442c0109008482000f0006511124808a0809202622214100a081000548402420188889080682040010a080504021412420121010003282014100850450402820400092100908030a094100a0802101383008404c2827060382008404a0802101242014100908028204c440a0809080988824200a080a0802820424014100a08006022a2201809090054442a2001808a080060241c094100a081000149412420907029282494040000a080504030b014100a080030228a080c08c2c0514128a000c08a0800302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1445 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_375 theta)
    · exact b4_1622 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_262 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1795 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_37 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2366 theta)
    · exact b4_2010 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1588 theta)
    · exact b4_2083 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1638 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2096 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_615 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2093 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_680 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_679 theta)
    · exact b4_1929 theta
    · exact b4_1924 theta
    · exact b4_75 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1073 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1469 theta)
    · exact b4_2088 theta
    · exact b4_1970 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1842 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1797 theta)
    · exact b4_2084 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1586 theta)
    · exact b4_2087 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_684 theta)
    · exact b4_2089 theta
    · exact b4_2031 theta
    · exact b4_2030 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_85 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1055 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_638 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_637 theta)
    · exact b4_2078 theta
    · exact b4_2080 theta
    · exact b4_2079 theta
theorem b3_2313 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2313 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(2,true),(4,true)),(false,(4,true),(0,true))] s3_2313 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00f000ff00f000ff00f000ff00f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffff0f0fffff0f0fffff0f0fffff0f0] (PetersenWireProjection.cons pc32w22 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w16 (PetersenWireProjection.cons pc32w13 rfl))))))))) (by decide +kernel)
theorem b3_2314 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2314 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,false))] s3_2314 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w27 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_2315 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2315 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_2315 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_2316 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2316 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true)),(false,(0,false),(5,true))] s3_2316 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w38 rfl)))))))))) (by decide +kernel)
theorem b3_2317 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2317 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_2317 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w39 rfl)))))))))) (by decide +kernel)
theorem b3_2318 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2318 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true)),(false,(0,false),(1,true))] s3_2318 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffffffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffaaaaffffaaaa] (PetersenWireProjection.cons pc34w35 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w40 rfl)))))))))) (by decide +kernel)
theorem b3_2319 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2319 := by
  apply PetersenIndexedNode.close (bank := [s4_1451,a5259,s4_1764,a5260,s4_2169,s4_2196,a5261,s4_2231,s4_2119,a5262,a5263,s4_2197,a5264,s4_2237,s4_2131,s4_2130,a5265,a5266,s4_2,a5267,a5268,s4_2232,s4_2143,a5269,a5270,s4_2199,s4_2158,a5271,a5272,s4_2201,s4_2176,a5273,a5274,s4_2203,a5275,s4_2193,s4_1142,a5276,s4_2219]) (PetersenIndexedNode.reasons 256 17 417 0x92128012a48492001002448002484a004c921248004008d2000c4442101108092000c2824800311118504c444480010809200100228008140020024420228002c0804202b0004800282012000b0205040240812000210148004008042022101800f8a8285415002115050a82a003c2101108098888420221012101185048404622230a090888840421011080a602050409800480032301200098086460240212000282048004007050402820800d8a8885445001d15110a88a0034282014101282850404a0221011210084044a0a2420108288404282021010a0209080280010808a0805000280814100a020420248401080a50100c049400480021201200094044240240112000060248004006109008480800b818080c05001903010180a002c84804240400500c04060221013130084050015626031300840406020301094140c042501108089888420225051311084144202060210808b0900c0406021410038281c042c240705018285040060203012484884809212480030b01200092126160248492000424048004004e002213018009109002602420280089080a0020424021204003e001c480a1505109005414210131300840454146260150508404848021011511109005444282080060a0805445000d15110a080848028200301109000c0484802322119000c04464403012120084804240488080c092200900041c124001220283824800a40000604900080050848042410009018100c0a0016030201814002042402120800300c080604420230b01080a000e616030b01080806040302108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030221a08848042404240018100c0886820302018110900424021205111141010808900048402400144449080490124000a080900080022420121010003282014102000a5040282040009210090802101242008404521228201084884045040210114849210052021505141005414210138300840454147060150508404a0802101151114100544428204c440a0805444988815110a080a08028200301141000c0416122a22018480c045444030105848a080160221201410084810001494124a0884809282212040000a08050400181141000604131228a080c4806045141018104c48a0801302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1451 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_377 theta)
    · exact b4_1764 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_162 theta)
    · exact b4_2169 theta
    · exact b4_2196 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1482 theta)
    · exact b4_2231 theta
    · exact b4_2119 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_175 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1770 theta)
    · exact b4_2197 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1460 theta)
    · exact b4_2237 theta
    · exact b4_2131 theta
    · exact b4_2130 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_942 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_949 theta)
    · exact b4_2 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_948 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1473 theta)
    · exact b4_2232 theta
    · exact b4_2143 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_179 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1768 theta)
    · exact b4_2199 theta
    · exact b4_2158 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_177 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1766 theta)
    · exact b4_2201 theta
    · exact b4_2176 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_195 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1145 theta)
    · exact b4_2203 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_941 theta)
    · exact b4_2193 theta
    · exact b4_1142 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_197 theta)
    · exact b4_2219 theta
theorem b3_2320 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2320 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_2320 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w50 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w42 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w41 rfl)))))))))) (by decide +kernel)
theorem b3_2321 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2321 := by
  apply PetersenIndexedNode.close (bank := [s4_1386,a5277,s4_2116,s4_2124,s4_1450,a5278,s4_2127,s4_2137,s4_1554,a5279,s4_2140,s4_2152,a5280,a5281,s4_2155,s4_2163,a5282,a5283,s4_2167,s4_2181,s4_1623,a5284,s4_2168,s4_2191,a5285,s4_273,s4_2170,s4_2205,s4_2113,a5286,a5287,s4_2138,s4_2114,a5288,a5289,s4_2153,s4_2115,a5290,a5291,s4_2164,s4_2117,a5292,a5293,s4_2182,s4_2118,a5294,a5295,s4_2192,s4_2120,s4_460,a5296,s4_2206,s4_2125,a5297,a5298,s4_2154,s4_2126,a5299,a5300,s4_2165,s4_2128,a5301,a5302,s4_2183,s4_2129,a5275,a5267,s4_2195,s4_2132,s4_598,a5303,s4_2207,s4_2139,a5304,a5305,s4_2166,s4_2141,a5306,a5307,s4_2184,s4_2142,a5308,a5309,s4_2198,s4_2144,s4_872,a5310,s4_2210,s4_2156,a5311,a5312,s4_2185,s4_2157,a5313,a5314,s4_2200,s4_2159,a5315,a5316,s4_2212,s4_2175,a5317,a5318,s4_2202,s4_2177,s4_940,a5319,s4_2214,s4_2186,a5320,a5321,s4_2216]) (PetersenIndexedNode.reasons 256 17 448 0x803731110a00050008036a4001850490008037b111185048444803624000a000500080352c0804202b0008034a4001410090008035ac081410090208034240004202900080331c08042027000803294000c282500080339c080c282502080321400042025000803126020504098008030a4001918090008031a60219180900880302400050409000802f1602050405800802e9400090805000802f9602090805008802e1400050405000802d0a02090802800802c8840450402800802d8a02050402808802c0840490802101802b250100c049400802aa400109009000802ba501109009004802a240000c0490008029150100c04540080289400189805000802995011898050048028140000c0450008027094140c0425018026884044c4421018027894144c4421058026084040c04210180250b0900c04060280248a0801c140e0280258b0901c14060a80240a0800c040602802324848260292008022a4001070290008023a4849070290128022240002602900080211080826025200802094000848050008021908088480420280201400026025000801f0a82826021301801e884046c482101801f8a8286c482a0a801e0840426021301801d0a88826021301801c8a08036121b01801d8a88836121309801c0a08026021301801b0180826021600801aa12002c081600801b818082c080602801a2120026021301801924404060491008018a4001070490008019a4405070490018018240000604900080171440406045100801694000c2c05000801794404c2c05001801614000060450008015084040604210080148a020424021008015884044240210180140a020060403028013125040604030280128a08016140b028013925041614030a80120a08006040302801121604060403028010818084a4806028011a16044a48212480100180806040302800f04c0442401300800e8581006041300800f84c0406041301800e0581042401604800d28888a0808404800ca400121009000800da888921009202800c24000a0809000800b1080921004202800a94000a0805000800b90808a0804202800a140012100500080090a828a0802a0a800888404e0c0210180098a828e0c02a0a800808404a080210180070a888a0802a2280068a0813110282080078a88931102a2280060a080a0802820800501808a0800602800485848a8880612800581808a8880602800405848a0801602800310900a0800301800284c052504030180039090125044240800204c04a0801301800100c08a0800302800084c48a2820312800180c08a2820302800004c48a0801302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1386 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1380 theta)
    · exact b4_2116 theta
    · exact b4_2124 theta
    · exact b4_1450 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_376 theta)
    · exact b4_2127 theta
    · exact b4_2137 theta
    · exact b4_1554 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1373 theta)
    · exact b4_2140 theta
    · exact b4_2152 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1555 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1372 theta)
    · exact b4_2155 theta
    · exact b4_2163 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1449 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_391 theta)
    · exact b4_2167 theta
    · exact b4_2181 theta
    · exact b4_1623 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_278 theta)
    · exact b4_2168 theta
    · exact b4_2191 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1625 theta)
    · exact b4_273 theta
    · exact b4_2170 theta
    · exact b4_2205 theta
    · exact b4_2113 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_878 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1646 theta)
    · exact b4_2138 theta
    · exact b4_2114 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1560 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1565 theta)
    · exact b4_2153 theta
    · exact b4_2115 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1559 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1564 theta)
    · exact b4_2164 theta
    · exact b4_2117 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_877 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1647 theta)
    · exact b4_2182 theta
    · exact b4_2118 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_461 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1481 theta)
    · exact b4_2192 theta
    · exact b4_2120 theta
    · exact b4_460 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1483 theta)
    · exact b4_2206 theta
    · exact b4_2125 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1640 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_883 theta)
    · exact b4_2154 theta
    · exact b4_2126 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1459 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_466 theta)
    · exact b4_2165 theta
    · exact b4_2128 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_616 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_618 theta)
    · exact b4_2183 theta
    · exact b4_2129 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_941 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_948 theta)
    · exact b4_2195 theta
    · exact b4_2132 theta
    · exact b4_598 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_690 theta)
    · exact b4_2207 theta
    · exact b4_2139 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1390 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1391 theta)
    · exact b4_2166 theta
    · exact b4_2141 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_465 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1461 theta)
    · exact b4_2184 theta
    · exact b4_2142 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_470 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1472 theta)
    · exact b4_2198 theta
    · exact b4_2144 theta
    · exact b4_872 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1632 theta)
    · exact b4_2210 theta
    · exact b4_2156 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_882 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1639 theta)
    · exact b4_2185 theta
    · exact b4_2157 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_873 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1631 theta)
    · exact b4_2200 theta
    · exact b4_2159 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_471 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1470 theta)
    · exact b4_2212 theta
    · exact b4_2175 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_600 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_688 theta)
    · exact b4_2202 theta
    · exact b4_2177 theta
    · exact b4_940 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_947 theta)
    · exact b4_2214 theta
    · exact b4_2186 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_642 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_639 theta)
    · exact b4_2216 theta
theorem b3_2322 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2322 := by
  apply PetersenIndexedNode.close (bank := [s4_1452,a5322,a5323,a5324,s4_2171,s4_2208,a5325,s4_2227,s4_2121,a5326,a5327,s4_2209,a5328,s4_2236,a5329,s4_2238,s4_2134,s4_2133,s4_599,a5330,s4_2,a5303,a5331,s4_2228,s4_2146,s4_2147,s4_2145,a5332,a5333,a5334,a5335,s4_2211,s4_2160,a5336,a5337,s4_2213,s4_2178,a5338,a5339,s4_2215,a5340,s4_2229,s4_2189,a5341,a5342,s4_2219,s4_598]) (PetersenIndexedNode.reasons 256 17 417 0x1002e800924002002892124800400b0a00050008015908088405002d21011080a005450002800400a0a0005000490930a0984050029614110a09242450002800400984202210180128a8285415002715050a82a004821011080a8888420221014909282014404a2225040288892424210110809c08042027000280018504a000702030a094080a00021012800400885040282080108a8885445002315110a88a0040282014102686850409a1249093230124249a1a6460248692424282049091602050405800280012100a0005808242014020a000282028000a0209080280010808a0805000280814100a020420248401080c007a003b001c800d818080c05001f03010180a00350019800c400580c0406024909212010c050017424021201242406020301150100c045400280031300a0005404626014010a00006022800094140c042501108089888420225051311084144202060210808b0900c0406021410038281c042c240705018285040060203014005600261301800a20e04260292128009a484a0024838141c0c004600209012210120e04840450006160140008404c2c021011400107025000150520e04541421018007084045415000f15050840507022101151120e045444282045c48a08054448b8915110a08107022820030120e040c0484808006212000c05000d0301212010702848080050848042410009018100c0a0016030201814002042402120800300c080604921241c120c0a000e838201c12484806040302288080c08a200500030b014000a202616028009400006045000108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c0884804240c2c0018100c0907020302018130b0042402120800214100a0810003484024202000a9080484040008a08050405111141014444921248402484944449080490124848a08092022101242008404500028201400084045040210114001210050001505141005414210138300840454147060150508404a0802101151114100544428204c440a0805444988815110a080a08028200301141000c0416122a22018480c045444030105848a080160241c094100a081000149412420907029282494040000a08050400181141000604131228a080c4806045141018104c48a0801302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1452 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_378 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1796 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_38 theta)
    · exact b4_2171 theta
    · exact b4_2208 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1484 theta)
    · exact b4_2227 theta
    · exact b4_2121 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_130 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1802 theta)
    · exact b4_2209 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1641 theta)
    · exact b4_2236 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_617 theta)
    · exact b4_2238 theta
    · exact b4_2134 theta
    · exact b4_2133 theta
    · exact b4_599 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_691 theta)
    · exact b4_2 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_690 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1633 theta)
    · exact b4_2228 theta
    · exact b4_2146 theta
    · exact b4_2147 theta
    · exact b4_2145 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_143 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1845 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1846 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1844 theta)
    · exact b4_2211 theta
    · exact b4_2160 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_52 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1587 theta)
    · exact b4_2213 theta
    · exact b4_2178 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_81 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1043 theta)
    · exact b4_2215 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_641 theta)
    · exact b4_2229 theta
    · exact b4_2189 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_86 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1056 theta)
    · exact b4_2219 theta
    · exact b4_598 theta
theorem b3_2323 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2323 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_2323 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w50 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons stored153 (PetersenWireProjection.cons pc29w54 (PetersenWireProjection.cons pc29w41 rfl)))))))))) (by decide +kernel)
theorem b3_2324 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2324 := by
  apply PetersenIndexedNode.close (bank := [s4_1624,a5343,a5344,s4_274,s4_2063,s4_2064,s4_1831,s4_25,a5345,a5346,s4_2172,s4_2217,s4_2122,s4_50,a5347,s4_2218,a5348,s4_2229,s4_2135,s4_77,a5349,s4_2219,a5350,s4_2233,s4_2148,s4_127,a5351,s4_2221,a5352,s4_2230,s4_2161,a5353,a5354,s4_2223,a5355,s4_2235,s4_2179,a5356,a5357,s4_2225,s4_2188,s4_2187,a5358,a5359,s4_2,a5321,a5320]) (PetersenIndexedNode.reasons 256 17 417 0x1002e8015240020058c4444800400b600565000801630a08a000c4448015b11120054c2826141400a6005084448013084044203002530a098506004e614130a0c0090420221017030084044202c444504038101c0c0a080703031110420221018011084044202c28230a0985060046614130a0b0a084202210180100a0805041001f2420121020042484024204007850402820800e0a0805040c444646032102003ac8c02460311105040282064440a0805040c28224201210191104840242030a08504028201404121005000210114100a0005010282014040840490802101800d018080c050019424021202003684804240400600c0406026222018080c04e060424031101888884806222381800c040602800b018080c04c282626031202002ec4c0426030a080c0406021282818084a0221011311084044a0a26221082884040c0421011612018080c04282007050380858480e0a03050a0800c040602800a04c0426030013212010902002a424021204004826021301800804c042602c44441c0b09020022838141c0b111026021301614104c042602c8882120109018504424021203222026021301150504c04260221011b12084045414362415050840426021301151104c04260228200d8486c0454441b0909848a08026021301030104c042c0084800b02058000c04160403012120026021301800700c080605000d30b018582001e616030b0400300604030262a280c080604c44441c1311118a8a83826222b11100604030264c480c080604c28230b0185819312616030b030a0806040302108080c08420028081090084004202212010808a0200604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030209808848026001604018104c002602030209808581042401604800540026001100072820141020016504028204001a000b0004622214100a081000348402420188889080682040008a08050406141242012101000128201410185045040282040001210090801505141005414210138300840454147060150508404a0802101151114100544428204c440a0805444988815110a080a08028200301141000c0416122a22018480c045444030105848a080160221201410006021301494100c0484809282212004c04a08013010181141000604131228a080c4806045141018104c48a0801302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1624 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_279 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1626 theta)
    · exact b4_274 theta
    · exact b4_2063 theta
    · exact b4_2064 theta
    · exact b4_1831 theta
    · exact b4_25 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2357 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2354 theta)
    · exact b4_2172 theta
    · exact b4_2217 theta
    · exact b4_2122 theta
    · exact b4_50 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1589 theta)
    · exact b4_2218 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_692 theta)
    · exact b4_2229 theta
    · exact b4_2135 theta
    · exact b4_77 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1075 theta)
    · exact b4_2219 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_1474 theta)
    · exact b4_2233 theta
    · exact b4_2148 theta
    · exact b4_127 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1799 theta)
    · exact b4_2221 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1471 theta)
    · exact b4_2230 theta
    · exact b4_2161 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_128 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1798 theta)
    · exact b4_2223 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_689 theta)
    · exact b4_2235 theta
    · exact b4_2179 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_78 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1074 theta)
    · exact b4_2225 theta
    · exact b4_2188 theta
    · exact b4_2187 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_643 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_640 theta)
    · exact b4_2 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_639 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_642 theta)
theorem b3_2325 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2325 := by
  intro m le c
  apply rejects_sound extra39 i7 6 tgt small39 hot39 [] s3_2325 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc39w65 (PetersenWireProjection.cons stored80 (PetersenWireProjection.cons stored79 (PetersenWireProjection.cons stored78 (PetersenWireProjection.cons stored77 (PetersenWireProjection.cons stored75 (PetersenWireProjection.cons stored74 (PetersenWireProjection.cons stored73 (PetersenWireProjection.cons pc39w60 (PetersenWireProjection.cons pc39w55 rfl)))))))))) (by decide +kernel)
theorem b3_2326 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2326 := by
  apply PetersenIndexedNode.close (bank := [s4_1453,a5360,s4_2,a5361,a5362,s4_2173,s4_2123,a5363,a5364,s4_2220,a5365,a5349,a5366,s4_2234,s4_2150,s4_2151,s4_2149,a5367,s4_2111,s4_2112,s4_2110,s4_2222,s4_2162,a5368,a5369,s4_2224,s4_2180,a5370,a5371,s4_2226,a5372,a5342,s4_1143,s4_1142]) (PetersenIndexedNode.reasons 256 17 408 0x8010c008120010002490924002003f001e28004000884045000622210808840492126141308098888c28242222484884044202800e084044203001b15050a82a003a2a0a15054006842022101511108404420292125040288094444a080511124848420221013111084044202420230a090808c444614121111080842022101800c0a0805041001715110a88a00322a22151140058504028204d0d0a081342492126460248493434c8c0490d248485040921225050a0809404420224201080894144840210510808504042021404121005000210114100a0005010282014040840490802101800a4004e0025001103010180a002a0602030140042001f000e6222018080c049212424021809888884806222248480c0406028006018080c04420262601080a001ac4c04260108080c0406021282818084a0221011311084044a0a26221082884040c0421011612018080c04282007050380858480e0a03050a0800c0406028005c002826030002212004c05242442404909311110702c240490920e052024c44421202404884048381210132220848042402101109008404c88841c09202854144240150508404c4c02101150518980541421012120084045444424015110a08117122820151122e245444282021200a0800c0442400301212008c8846400301119100c0484802120109020010212010904001c06040302800480c08060500061090084818a8a03020181248490704830262a2a0e09888a9212018100c0993120302018110808c2c0420264c498580c2c04202018100c084202030210800a0204240210010808848042022808018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c08868221201090109000604030221a080c0806044240109008482000b00048001c0008a08050405111141014444921248402484944449080490124848a08092022101242008404521228201084884045040210114849210052021505141005414210138300840454147060150508404a0802101151114100544428204c440a0805444988815110a080a08028200301141000c0416122a22018480c045444030105848a08016022120141008481000149412420884809282212040000a08050400181141000604131228a080c4806045141018104c48a0801302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_1453 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_379 theta)
    · exact b4_2 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_2471 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_2470 theta)
    · exact b4_2173 theta
    · exact b4_2123 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_13 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_1829 theta)
    · exact b4_2220 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1076 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1075 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1475 theta)
    · exact b4_2234 theta
    · exact b4_2150 theta
    · exact b4_2151 theta
    · exact b4_2149 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_23 theta)
    · exact b4_2111 theta
    · exact b4_2112 theta
    · exact b4_2110 theta
    · exact b4_2222 theta
    · exact b4_2162 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_15 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1827 theta)
    · exact b4_2224 theta
    · exact b4_2180 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_18 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_1178 theta)
    · exact b4_2226 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1057 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1056 theta)
    · exact b4_1143 theta
    · exact b4_1142 theta
theorem b3_2327 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2327 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,false))] s3_2327 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w78 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w71 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2328 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2328 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s3_2328 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w78 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w80 rfl)))))))))) (by decide +kernel)
theorem b3_2329 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2329 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false))] s3_2329 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f00000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w81 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2330 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2330 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s3_2330 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w83 rfl)))))))))) (by decide +kernel)
theorem b3_2331 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2331 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true))] s3_2331 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w85 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2332 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2332 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false))] s3_2332 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w86 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2333 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2333 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(6,true))] s3_2333 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2334 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2334 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(2,true))] s3_2334 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w83 rfl)))))))))) (by decide +kernel)
theorem b3_2335 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2335 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s3_2335 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w89 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w80 rfl)))))))))) (by decide +kernel)
theorem b3_2336 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2336 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,true)),(false,(0,true),(5,true))] s3_2336 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0f0fffff0f0fffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w90 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2337 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2337 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(5,true))] s3_2337 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0a0affff0a0affff0a0affff0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w93 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2338 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2338 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(0,true)),(false,(0,true),(5,true))] s3_2338 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5555ffff5555ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w95 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2339 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2339 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(5,true))] s3_2339 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff5050ffff5050ffff5050ffff5050,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w97 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2340 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2340 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,true)),(false,(0,true),(5,true))] s3_2340 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffffaaaaffffaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w99 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2341 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2341 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(6,true)),(false,(0,true),(5,true))] s3_2341 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000fffff0f0fffff0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons pc26w101 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2342 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2342 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(0,true),(7,true))] s3_2342 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0f0f00000f0f0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w102 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2343 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2343 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,true)),(false,(0,true),(7,true))] s3_2343 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0a0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w104 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2344 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2344 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,true)),(false,(0,true),(7,true))] s3_2344 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff5555000055550000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w106 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2345 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2345 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(0,true)),(false,(0,true),(7,true))] s3_2345 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff5050505050505050,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w108 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2346 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2346 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,true)),(false,(0,true),(7,true))] s3_2346 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000aaaa0000aaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w110 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2347 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2347 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,true)),(false,(0,true),(7,true))] s3_2347 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffff0000f0f00000f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w111 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2348 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2348 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(6,false)),(false,(0,true),(5,true))] s3_2348 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffaaaaffffaaaaffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w112 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2349 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2349 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false)),(false,(0,true),(7,true))] s3_2349 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w113 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2350 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2350 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false)),(false,(0,true),(5,true))] s3_2350 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffff0f0fffff0f0ffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w115 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_2351 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_2351 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,false),(4,false)),(false,(0,true),(7,true))] s3_2351 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f00000f0f00000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w116 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
