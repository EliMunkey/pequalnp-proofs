import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S6
import Q1020K12L4S8
import Q1020K12L4S9
import Q1020K12L4S13
import Q1020K12L4S18
import Q1020K12L4S21
import Q1020K12L4S22
import Q1020K12L4S24
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S59
import Q1020K12L4S60
import Q1020K12L4S61
import Q1020K12L4S63
import Q1020K12L4S65
import Q1020K12L4S67
import Q1020K12L4S69
import Q1020K12L4S71
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc29w1 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored156 stored154 rfl rfl

private theorem pc29w0 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc29w1 stored153 rfl rfl
private theorem pc29w5 : PetersenPackedPin.project extra29 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored153 stored154 rfl rfl





private theorem pc29w11 : PetersenPackedPin.project extra29 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f := PetersenWireProjection.derive 1 pc29w1 stored153 rfl rfl


private theorem pc37w13 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored66 stored71 rfl rfl

private theorem pc37w12 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 pc37w13 stored67 rfl rfl
private theorem pc37w17 : PetersenPackedPin.project extra37 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored67 stored66 rfl rfl





private theorem pc37w23 : PetersenPackedPin.project extra37 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc37w13 stored67 rfl rfl




private theorem pc26w26 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl

private theorem pc26w29 : PetersenPackedPin.project extra26 (0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 3 stored2 stored7 rfl rfl



private theorem pc26w34 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f00000f0f0000 := PetersenWireProjection.derive 1 pc26w26 stored0 rfl rfl




private theorem pc30w37 : PetersenPackedPin.project extra30 (0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored10 stored13 rfl rfl

private theorem pc30w40 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl



private theorem pc30w45 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaa00000000ffaaffaa := PetersenWireProjection.derive 1 pc30w40 stored8 rfl rfl



private theorem pc117w47 : PetersenPackedPin.project extra117 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored122 stored123 rfl rfl

private theorem pc117w50 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored123 stored124 rfl rfl




private theorem pc117w56 : PetersenPackedPin.project extra117 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 1 pc117w50 stored121 rfl rfl
private theorem pc26w57 : PetersenPackedPin.project extra26 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored6 stored7 rfl rfl




private theorem pc32w60 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored26 stored29 rfl rfl


private theorem pc32w64 : PetersenPackedPin.project extra32 (0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored28 stored29 rfl rfl


private theorem pc32w68 : PetersenPackedPin.project extra32 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a := PetersenWireProjection.derive 1 pc32w60 stored24 rfl rfl


private theorem pc116w69 : PetersenPackedPin.project extra116 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffff := PetersenWireProjection.derive 3 stored105 stored111 rfl rfl


private theorem pc116w73 : PetersenPackedPin.project extra116 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccccccccccc := PetersenWireProjection.derive 3 stored107 stored111 rfl rfl




private theorem pc116w79 : PetersenPackedPin.project extra116 (0xffffffffccccccccffffffffcccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc116w73 stored105 rfl rfl








private theorem pc73w89 : PetersenPackedPin.project extra73 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored130 stored135 rfl rfl
private theorem pc73w88 : PetersenPackedPin.project extra73 (0xffffffff00000000cccccccc00000000ffffffff00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w89 stored131 rfl rfl
private theorem pc73w90 : PetersenPackedPin.project extra73 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc73w89 stored129 rfl rfl
private theorem pc26w91 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w93 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w92 : PetersenPackedPin.project extra26 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc26w93 stored0 rfl rfl








private theorem pc34w102 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w104 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w103 : PetersenPackedPin.project extra34 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w104 stored16 rfl rfl
private theorem pc30w105 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored11 stored13 rfl rfl
private theorem pc30w107 : PetersenPackedPin.project extra30 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff0fff0fff0fff0fff0fff0fff0 := PetersenWireProjection.derive 3 stored9 stored14 rfl rfl
private theorem pc30w106 : PetersenPackedPin.project extra30 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xfff0fff000000000fff0fff0 := PetersenWireProjection.derive 1 pc30w107 stored8 rfl rfl
private theorem pc32w108 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored27 stored28 rfl rfl
private theorem pc32w110 : PetersenPackedPin.project extra32 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored25 stored29 rfl rfl
private theorem pc32w109 : PetersenPackedPin.project extra32 (0xffffffffffffffffcccccccccccccccc : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc32w110 stored24 rfl rfl
private theorem pc34w111 : PetersenPackedPin.project extra34 (0xffff000000000000ffff000000000000ffff000000000000ffff00000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored18 stored19 rfl rfl
private theorem pc34w112 : PetersenPackedPin.project extra34 (0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored17 stored19 rfl rfl
private theorem pc34w113 : PetersenPackedPin.project extra34 (0xffff0000ffff0000cccc0000cccc0000ffff0000ffff0000cccc0000cccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc34w104 stored19 rfl rfl
private theorem pc34w114 : PetersenPackedPin.project extra34 (0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored16 stored19 rfl rfl
private theorem pc26w115 : PetersenPackedPin.project extra26 (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored4 stored7 rfl rfl
private theorem pc32w116 : PetersenPackedPin.project extra32 (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored28 stored29 rfl rfl
private theorem pc30w117 : PetersenPackedPin.project extra30 (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored12 stored13 rfl rfl
private theorem pc32w118 : PetersenPackedPin.project extra32 (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 1 stored27 stored28 rfl rfl
private theorem pc32w119 : PetersenPackedPin.project extra32 (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored26 stored28 rfl rfl
private theorem pc32w120 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored25 stored28 rfl rfl
private theorem pc32w121 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00cc00cc00cc00cc00ff00ff00ff00ff00cc00cc00cc00cc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 1 pc32w110 stored28 rfl rfl
private theorem pc32w122 : PetersenPackedPin.project extra32 (0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored24 stored28 rfl rfl
private theorem pc26w123 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w124 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl
private theorem pc26w125 : PetersenPackedPin.project extra26 (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored4 stored7 rfl rfl
private theorem pc26w126 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored3 stored7 rfl rfl
private theorem pc26w127 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w128 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w129 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa8888888888888888aaaaaaaaaaaaaaaa8888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w128 pc26w123 rfl rfl
private theorem pc26w130 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w133 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w132 : PetersenPackedPin.project extra26 (0x222222222222222200000000000000002222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 pc26w133 stored1 rfl rfl
private theorem pc26w131 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000002222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w132 pc26w130 rfl rfl
private theorem pc26w135 : PetersenPackedPin.project extra26 (0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 pc26w57 stored1 rfl rfl
private theorem pc26w136 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w134 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffeeeeeeeeeeeeeeee : BitVec 256) = 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a := PetersenWireProjection.derive 1 pc26w135 pc26w136 rfl rfl
theorem b3_1596 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1596 := by
  intro m le c
  apply rejects_sound extra29 i7 6 tgt small29 hot29 [] s3_1596 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc29w11 (PetersenWireProjection.cons stored160 (PetersenWireProjection.cons stored154 (PetersenWireProjection.cons stored159 (PetersenWireProjection.cons stored158 (PetersenWireProjection.cons stored157 (PetersenWireProjection.cons stored156 (PetersenWireProjection.cons stored155 (PetersenWireProjection.cons pc29w5 (PetersenWireProjection.cons pc29w0 rfl)))))))))) (by decide +kernel)
theorem b3_1597 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1597 := by
  apply PetersenIndexedNode.close (bank := [a4640,s4_2514,s4_338,a4641,s4_963,a4642,s4_1086,s4_1096,s4_2925,a4643,s4_1091,s4_1095,s4_1081,s4_1061,s4_1058,s4_1048,s4_1101,s4_1039,s4_1103,a4644,a4630]) (PetersenIndexedNode.reasons 256 17 426 0x188884202210121010c4448404622218888c444840421011080a002900135000210114100a000311128200c4444202706010808c444e0c0311110809410042024808141012000840438302400120207060480821010a0808404280824200a0004202282014000a020504028081080921004202800894100a080a08038301c18200247060383028200a080504046061210118088404141021011181828204206210109080840424040a0809000420224201200090104840240410808504042025444121009080a08014100a08151102820141028200908048404c440a080504050401c180e081311038301418141005040282042020180908009010131121001080826224202240400c0406022606018080c0442026260108089818c4c02406108080c0406028007818080c04a08013110988a002026221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060280074003506028404131220c06001626241312210120018840421010989084044808313012020840462602101120204c484808514120e054500a080131209891450426241312282010702a0804941098904c4850401b1a0d89125043634131a141004c4826241511098905440282045c48a08054448b8914110a0804c4828200301189800c0484801312098800c042624030121200c4c06260428280c08060484041090210110a0a21204202a101006040302248480c080604420230b010808921261602404908080604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030241c08848042402624018100c090702030201810989042402120800540026001084045010210120016a02049092101200088404210128080840448087030120208404e060210112021404048088003400150848a080501028082000ea0205010282020008a080383028081404050405818280c0e0c0b0305810141014040a02014102808050404840800112100504100031410121014040a0200301280800c0484805212280900c04a4240301212014040a02013122808006028381511100c044c48a222511020e054040a02001812808006048382800020e0806050001018120e094040a020)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_384 theta)
    · exact b4_2514 theta
    · exact b4_338 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2532 theta)
    · exact b4_963 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2669 theta)
    · exact b4_1086 theta
    · exact b4_1096 theta
    · exact b4_2925 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2911 theta)
    · exact b4_1091 theta
    · exact b4_1095 theta
    · exact b4_1081 theta
    · exact b4_1061 theta
    · exact b4_1058 theta
    · exact b4_1048 theta
    · exact b4_1101 theta
    · exact b4_1039 theta
    · exact b4_1103 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_918 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_917 theta)
theorem b3_1598 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1598 := by
  intro m le c
  apply rejects_sound extra37 i7 6 tgt small37 hot37 [] s3_1598 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc37w23 (PetersenWireProjection.cons stored72 (PetersenWireProjection.cons stored71 (PetersenWireProjection.cons stored70 (PetersenWireProjection.cons stored69 (PetersenWireProjection.cons stored68 (PetersenWireProjection.cons stored66 (PetersenWireProjection.cons stored65 (PetersenWireProjection.cons pc37w17 (PetersenWireProjection.cons pc37w12 rfl)))))))))) (by decide +kernel)
theorem b3_1599 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1599 := by
  apply PetersenIndexedNode.close (bank := [a4645,s4_2515,s4_2925,a4628,s4_1091,s4_1078,s4_1076,s4_1062,s4_1058,s4_1049,s4_1102,s4_1085,s4_1057,s4_1035,s4_1033]) (PetersenIndexedNode.reasons 256 17 414 0x1888848086202210108404420262221080884048404240421012001d000d5000210105414a00031110a828c4044202706010808c444e0c0211110808541442024808141012000840438302400120207060480821010a0808404280824200a0004202282014000a0205040280810809210042021d0d1410074142a0a38300a82874347060150d0a828a0802a0a46061210118088404141021011181828204206210109080840424040a0809000420224201200090104840240410808504042021505121005404a08014100a80854142820150528200908048404c440a080504050401c180e08131103830141814100504028204202400310800901003012100108080602030124042001690102606018080c0442026260108089818c4c02406108080c0406028004818080c042a0a13110980a0014262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c04060280044001d06028404131220c0484042624210112020c4c0480821011898084044808131212020541483811505282004c4826241505098905014a08041c08a029250426241312141006c68362449410d8d04c6850401312098905444262415100a08117122820151122e245044282013120a0800c0462600301212004c4826200301098900c0484803130189810a0b000642822101006040302428280c08060484048002a101092120302018110808c2c0420224849858090124202018100c094302030201810a8284240230250c08848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c09070221201090098900604030241c080c08060426241090084820009000380012101124248404210124848840448087030120208404e0602101120212424c2021505248485414a0805010280805414a0205101282012424a20238302808140405040490924848e0c0921249011410140409202141024849242448404d0d2486850409a1a4d0912101242492120301248480c0484805212280900c04a42403012120124248602131228081202483814909240484c489212490920e054040a02001812484806048382800000e0806050001018120e0924248302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_386 theta)
    · exact b4_2515 theta
    · exact b4_2925 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2918 theta)
    · exact b4_1091 theta
    · exact b4_1078 theta
    · exact b4_1076 theta
    · exact b4_1062 theta
    · exact b4_1058 theta
    · exact b4_1049 theta
    · exact b4_1102 theta
    · exact b4_1085 theta
    · exact b4_1057 theta
    · exact b4_1035 theta
    · exact b4_1033 theta
theorem b3_1600 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1600 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1600 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w29 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1601 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1601 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1601 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w45 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1602 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1602 := by
  intro m le c
  apply rejects_sound extra117 i6 5 tgt small117 hot117 [] s3_1602 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffffffffffff,0xffff0000ffff0000,0xcccccccccccccccc,0xaaaaaaaaaaaaaaaa,0xffffffff00000000,0xff00ff00ff00ff00,0xffffffffffffffff,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0x0] (PetersenWireProjection.cons pc117w56 (PetersenWireProjection.cons stored128 (PetersenWireProjection.cons stored124 (PetersenWireProjection.cons stored127 (PetersenWireProjection.cons stored126 (PetersenWireProjection.cons stored125 (PetersenWireProjection.cons pc117w50 (PetersenWireProjection.cons stored122 (PetersenWireProjection.cons pc117w47 (PetersenWireProjection.cons stored121 rfl)))))))))) (by decide +kernel)
theorem b3_1603 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1603 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(0,true),(3,true)),(false,(0,true),(6,true))] s3_1603 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffaaffaa00000000ffaaffaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w45 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w37 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_1604 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1604 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(4,true)),(false,(0,true),(3,true))] s3_1604 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w34 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w57 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w26 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1605 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1605 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(6,true),(0,true)),(false,(0,true),(3,true))] s3_1605 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0f0f0f0f0f0f0a0a0a0a0a0a0a0a,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w68 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w64 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons pc32w60 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1606 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1606 := by
  intro m le c
  apply rejects_sound extra116 i6 5 tgt small116 hot116 [] s3_1606 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xaaaaaaaaaaaaaaaa,0xffff0000ffff0000,0xff00ff00ff00ff00,0xffffffff00000000,0x0,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffffffffffffffff,0xffffffffffffffff] (PetersenWireProjection.cons pc116w79 (PetersenWireProjection.cons stored112 (PetersenWireProjection.cons stored110 (PetersenWireProjection.cons stored109 (PetersenWireProjection.cons stored108 (PetersenWireProjection.cons stored107 (PetersenWireProjection.cons pc116w73 (PetersenWireProjection.cons stored106 (PetersenWireProjection.cons stored105 (PetersenWireProjection.cons pc116w69 rfl)))))))))) (by decide +kernel)
theorem b3_1607 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1607 := by
  apply PetersenIndexedNode.close (bank := [a4646,s4_2516,a4647,a4648,a4649,s4_1114,a4650,a4651,s4_779,a4652,s4_1065,s4_1120,s4_1077,s4_1073,s4_1050,s4_1121,s4_1051,s4_1118,s4_1110,s4_1055,s4_1040,s4_1119,a4653,a4637,a4654,s4_1122,s4_1113,s4_1036,s4_1116,a4655]) (PetersenIndexedNode.reasons 256 17 420 0x6222120218808840421011080988884202210121010901084041312400750602840441c0a0c044c48838113122101200388404210120e04840448086160120208404c2c02101120210702480813124006c4c4884041505210104c482a0a1405210120034840431110a828c4044202800c10808c445001921111080854144202800bc00594100838115050a829202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a020420248401080a00285040282020e04e0c07060800a9c180e0c08381282014100743450401d050a828e0c02a0a1d0d1c18054342a0a28200a829181828204602210105444840446060a8890818840414102101090102820240010808908048002404121009010420214101080917124840242020e045040282045c48a080504083812420121005414484015012820850402a0215050a0805414a08224201210131102820141014100706038204c440e0c05060504014100a081080900134200240400c0484004202018080c04901080092404098180602030110809898042022606313009018420203010180a00208480424020e040c0406028008818080c048381424021202001c060203010a8284c4426028007898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018090a0a212042822101006040302428280c080604840410902101092120302018110808c2c0420224849858090124202018100c090703000d41c030b000604030241c080c080604c2c0800630b020014030201810a8284240230280058848042402a0a018100c08a28203020181141002624130228a084c4806245040018100c089282030201810a08016140b0224a082c2806142820018100c090b0203020181018084a48060242c08949042480602018100c084c490009131221011242484041312248492424840480042101084049212210112022000c480821014001c8404480849093080a000b0004480920e05242490121505248485414a0825011280885414a0225001282092424a00238302808940445040490924848e0c0921249011410140449202141024849242448404d0d2486850409a1a4d0912101242492120301248480c0484808001212000c0500030301212012424860201812484806048382800000e0806050001018120e0924248302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_387 theta)
    · exact b4_2516 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_283 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2573 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_2743 theta)
    · exact b4_1114 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_158 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2821 theta)
    · exact b4_779 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2982 theta)
    · exact b4_1065 theta
    · exact b4_1120 theta
    · exact b4_1077 theta
    · exact b4_1073 theta
    · exact b4_1050 theta
    · exact b4_1121 theta
    · exact b4_1051 theta
    · exact b4_1118 theta
    · exact b4_1110 theta
    · exact b4_1055 theta
    · exact b4_1040 theta
    · exact b4_1119 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_573 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_572 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_560 theta)
    · exact b4_1122 theta
    · exact b4_1113 theta
    · exact b4_1036 theta
    · exact b4_1116 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_91 theta)
theorem b3_1608 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1608 := by
  intro m le c
  apply rejects_sound extra73 i6 5 tgt small73 hot73 [] s3_1608 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000,0xffffffff00000000,0xaaaaaaaaaaaaaaaa,0x0,0xcccccccccccccccc] (PetersenWireProjection.cons pc73w90 (PetersenWireProjection.cons pc73w88 (PetersenWireProjection.cons stored136 (PetersenWireProjection.cons stored135 (PetersenWireProjection.cons stored134 (PetersenWireProjection.cons stored133 (PetersenWireProjection.cons stored132 (PetersenWireProjection.cons stored131 (PetersenWireProjection.cons stored130 (PetersenWireProjection.cons stored129 rfl)))))))))) (by decide +kernel)
theorem b3_1609 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1609 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1609 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w91 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1610 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1610 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(4,true)),(false,(7,true),(0,true))] s3_1610 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1611 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1611 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(4,true)),(false,(7,true),(0,true))] s3_1611 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w104 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1612 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1612 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(4,true)),(false,(7,true),(0,true))] s3_1612 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w102 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_1613 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1613 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(2,true)),(false,(6,true),(0,true))] s3_1613 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w106 (PetersenWireProjection.cons pc30w105 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1614 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1614 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1614 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w108 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1615 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1615 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_1615 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w111 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1616 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1616 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_1616 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xffff0000ffff0000ffff0000ffff0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w112 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1617 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1617 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_1617 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w113 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1618 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1618 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true)),(false,(7,true),(0,true))] s3_1618 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffaaaaffffaaaa,0xffffffffffffffff0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w103 (PetersenWireProjection.cons pc34w114 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b3_1619 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1619 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1619 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w115 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1620 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1620 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1620 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w116 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1621 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1621 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1621 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w116 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons pc32w110 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1622 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1622 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,true),(3,true)),(false,(6,true),(0,true))] s3_1622 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xfff0fff000000000fff0fff0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w106 (PetersenWireProjection.cons pc30w117 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b3_1623 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1623 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1623 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w118 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1624 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1624 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1624 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffffffffffffffff0000000000000000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w119 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1625 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1625 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1625 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w120 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1626 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1626 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1626 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w121 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1627 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1627 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1627 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc32w109 (PetersenWireProjection.cons pc32w122 (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons stored27 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 rfl)))))))))) (by decide +kernel)
theorem b3_1628 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1628 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1628 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w123 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1629 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1629 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1629 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w124 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1630 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1630 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1630 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w125 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1631 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1631 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1631 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w126 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1632 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1632 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1632 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w127 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1633 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1633 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1633 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w128 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1634 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1634 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1634 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w129 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1635 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1635 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1635 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w130 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1636 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1636 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1636 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons pc26w131 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_1637 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_1637 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true)),(false,(3,true),(0,true))] s3_1637 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0x0,0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w92 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w134 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
