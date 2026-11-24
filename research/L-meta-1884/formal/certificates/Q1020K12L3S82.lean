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
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S16
import Q1020K12L4S19
import Q1020K12L4S21
import Q1020K12L4S23
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S30
import Q1020K12L4S36
import Q1020K12L4S38
import Q1020K12L4S39
import Q1020K12L4S42
import Q1020K12L4S43
import Q1020K12L4S50
import Q1020K12L4S55
import Q1020K12L4S56
import Q1020K12L4S57
import Q1020K12L4S58
import Q1020K12L4S62
import Q1020K12L4S63
import Q1020K12L4S64
import Q1020K12L4S65
import Q1020K12L4S66
import Q1020K12L4S74
import Q1020K12L4S75
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0



private theorem pc26w1 : PetersenPackedPin.project extra26 (0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored7 rfl rfl


private theorem pc26w6 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl

private theorem pc26w5 : PetersenPackedPin.project extra26 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xeeeecccceeeecccceeeecccceeeecccc := PetersenWireProjection.derive 3 pc26w6 stored3 rfl rfl





private theorem pc0w12 : PetersenPackedPin.project cycle0 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored50 stored55 rfl rfl

private theorem pc0w17 : PetersenPackedPin.project cycle0 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored50 stored55 rfl rfl

private theorem pc0w16 : PetersenPackedPin.project cycle0 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc0w17 stored52 rfl rfl






private theorem pc30w23 : PetersenPackedPin.project extra30 (0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored9 stored13 rfl rfl


private theorem pc30w28 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl

private theorem pc30w27 : PetersenPackedPin.project extra30 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xfffffffffffffffff000f000f000f000 := PetersenWireProjection.derive 3 pc30w28 stored11 rfl rfl





private theorem pc34w34 : PetersenPackedPin.project extra34 (0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 3 stored17 stored19 rfl rfl


private theorem pc34w39 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w38 : PetersenPackedPin.project extra34 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 3 pc34w39 stored19 rfl rfl



private theorem pc0w44 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored50 stored51 rfl rfl
private theorem pc26w45 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored7 rfl rfl


private theorem pc3w46 : PetersenPackedPin.project cycle3 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored33 stored39 rfl rfl


private theorem pc3w52 : PetersenPackedPin.project cycle3 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored34 stored39 rfl rfl

private theorem pc3w51 : PetersenPackedPin.project cycle3 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc3w52 stored36 rfl rfl





private theorem pc32w57 : PetersenPackedPin.project extra32 (0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored24 stored28 rfl rfl



private theorem pc32w63 : PetersenPackedPin.project extra32 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored25 stored29 rfl rfl

private theorem pc32w62 : PetersenPackedPin.project extra32 (0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xffaaff00ffaaff00ffaaff00ffaaff00 := PetersenWireProjection.derive 3 pc32w63 stored27 rfl rfl


private theorem pc0w69 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored52 rfl rfl
private theorem pc0w68 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffccccffffccccffff0000ffff0000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 pc0w69 pc0w17 rfl rfl
private theorem pc0w70 : PetersenPackedPin.project cycle0 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xff00ff00 := PetersenWireProjection.derive 3 stored49 stored50 rfl rfl


private theorem pc1w71 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored57 stored59 rfl rfl


private theorem pc1w76 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 stored57 stored60 rfl rfl
private theorem pc1w78 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 3 stored59 stored60 rfl rfl
private theorem pc1w75 : PetersenPackedPin.project cycle1 (0xffffffffffff0000ffffffffffff0000ffff0000ffff0000ffff0000ffff0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc1w76 pc1w78 rfl rfl




theorem b3_3444 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3444 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s3_3444 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w5 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_3445 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3445 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3445 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xcccccccc,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w16 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w12 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3446 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3446 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(3,false)),(false,(7,true),(0,true))] s3_3446 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xfffffffffffffffff000f000f000f000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons pc30w27 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons pc30w23 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b3_3447 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3447 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s3_3447 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons pc34w38 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w34 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b3_3448 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3448 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3448 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xffff0000,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w16 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons pc0w44 (PetersenWireProjection.cons stored49 rfl))))))))) (by decide +kernel)
theorem b3_3449 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3449 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(4,false)),(false,(2,true),(0,true))] s3_3449 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xeeeecccceeeecccceeeecccceeeecccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons pc26w5 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w45 rfl))))))))) (by decide +kernel)
theorem b3_3450 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3450 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_3450 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons pc3w51 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 (PetersenWireProjection.cons pc3w46 rfl))))))))) (by decide +kernel)
theorem b3_3451 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3451 := by
  intro m le c
  apply rejects_sound extra32 i7 10 tgt (small32 theta) hot32 [(false,(4,false),(0,false)),(false,(4,true),(0,true))] s3_3451 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0x0,0xffaaff00ffaaff00ffaaff00ffaaff00,0xffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored31 (PetersenWireProjection.cons stored29 (PetersenWireProjection.cons stored30 (PetersenWireProjection.cons stored28 (PetersenWireProjection.cons pc32w62 (PetersenWireProjection.cons stored26 (PetersenWireProjection.cons stored25 (PetersenWireProjection.cons stored24 (PetersenWireProjection.cons pc32w57 rfl))))))))) (by decide +kernel)
theorem b3_3452 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3452 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3452 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w16 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w68 rfl))))))))) (by decide +kernel)
theorem b3_3453 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3453 := by
  apply PetersenIndexedNode.close (bank := [a6550,s4_3141,a6551,s4_185,a6552,s4_3135,a6553,a6554,s4_2776,s4_210,a6555,s4_3136,a6556,s4_3144,a6557,a6558,a6559,s4_3137,a6560,s4_3142,a6561,a6562,a6563,s4_3138,a6564,s4_3145,s4_3128,a6565,a6566,s4_3139,a6567,a6568,s4_987,a6569,s4_9,a6570,a6571,a6572,a6573,s4_3140,s4_986]) (PetersenIndexedNode.reasons 256 17 417 0x100288010210120044a0204202400989010480880129c0c0e061002738181c0c200484808240438180901048085010322214040e0606444281814040480824044008e004221018011282004202a0208010a80820040a08050404007e003c8424381828200e0604808706012020e060e0c038181202141004808800e14100a081001b38301c182003a7060383040068a08050405818141016040a02048402808160609080501828080a080a020280824200a0004808282014000a020504028081202121004808800c14100a080a08038301c18200327060383028200a0805040800b121009081001514100a082002e28201410400509080484080090a0805040a0206460280820026c8c06460280805040282024040a0809000501024201200090104840240414040504050105444121009080a08014100a08151102820141028200908048404c440a080504050401c180e08131103830141814100504028208008018080c05000f13110988a002226221311400380c0406025212018080c04a020424028081484884805012280800c0406022606018080c0448086260120209818c4c02406120200c0406028006018080c04a08013110988a001a26221311282000c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602800500c04060300091312098920016262413124002006020301511100c040602a02041c0a80814444838150112808006020301210900c04060248088003120208425000724051202006020301514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301800200c0806050003109008482000a212010904000806040302800000c080604a02041c1280820002838241c12808006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b4_1524 theta)
    · exact b4_3141 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_2427 theta)
    · exact b4_185 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1784 theta)
    · exact b4_3135 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_990 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3172 theta)
    · exact b4_2776 theta
    · exact b4_210 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1175 theta)
    · exact b4_3136 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1512 theta)
    · exact b4_3144 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2433 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_188 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1776 theta)
    · exact b4_3137 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1520 theta)
    · exact b4_3142 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2430 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_191 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_1779 theta)
    · exact b4_3138 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_1297 theta)
    · exact b4_3145 theta
    · exact b4_3128 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_219 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1301 theta)
    · exact b4_3139 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2689 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_2679 theta)
    · exact b4_987 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_998 theta)
    · exact b4_9 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_997 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_2779 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_213 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_1172 theta)
    · exact b4_3140 theta
    · exact b4_986 theta
theorem b3_3454 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3454 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s3_3454 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0x0,0x0,0xffff0000,0x0,0xff00ff00,0xff00ff00] (PetersenWireProjection.cons stored56 (PetersenWireProjection.cons stored55 (PetersenWireProjection.cons stored54 (PetersenWireProjection.cons stored53 (PetersenWireProjection.cons pc0w16 (PetersenWireProjection.cons stored51 (PetersenWireProjection.cons stored50 (PetersenWireProjection.cons stored49 (PetersenWireProjection.cons pc0w70 rfl))))))))) (by decide +kernel)
theorem b3_3455 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3455 := by
  apply PetersenIndexedNode.close (bank := [a6574,s4_3154,s4_2449,a6575,a6576,s4_3148,a6577,s4_3157,a6578,a6579,s4_2731,a6580,a6581,s4_3149,a6582,a6583,a6584,s4_3150,a6585,s4_3158,a6586,s4_3155,a6587,a6588,a6589,a6590,a6591,a6592,a6593,s4_3151,a6594,s4_3159,a6595,a6596,s4_3146,a6597,a6598,s4_3152,a6599,a6600,a6601,a6602,s4_10,a6603,a6604,a6605,s4_3156,a6606,a6607,a6608,s4_3153]) (PetersenIndexedNode.reasons 256 17 417 0xa0208018a8081080900304202280820064a0204202400bd0808c4443111380810809002d420231112005cc4444202188890809002c80141202200546222240428080c282a0204202383010808a020706028081080861414202400ae005221018015185044202622280149888a0050614130a0c009e004c42224808141012000840448402400120209080480821010a080840480122420121010023282014102004a504028204008921009080311124200e041002128201c080c444504031114008121009080800f14100a080614138301c102003e7060283018504a080504046060a081180884046460210111818c8c042062101050408404800e4006e0035001914100a082003a2820141040062002f0016800a0a0805040622224201a082002a4840242018888504028208009121009080614114100a08200262820141018504908048404c440a0805040504015110e08131102a221511141005040282042020180908009010424021001080884804202240400c0406028008018080c05000f13110988a002226221311400380c0406023a1a018080c046222626018888e868c4c0381a188880c04060232a2818080c046141131109888ca8a26221311185040c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602490900c040602840441c0a0c052424838148092101006020301800600c040603000b131a098d2001a2634131a4002806020301311100c04060270308004188c0c445000931111c0c006020301800300c0406026141131a098d2000e2634131a1850406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c04060403012120006020301428280c080604840441c120c090a0a83824202a101006040302800200c0806050003109008482000a212010904000806040302800000c080604622230b0184820002616010b0188880604030230a080c080604e0c0109008480c28221201090383000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym6 fix6 (by decide +kernel) (b4_1525 theta)
    · exact b4_3154 theta
    · exact b4_2449 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_138 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1817 theta)
    · exact b4_3148 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_806 theta)
    · exact b4_3157 theta
    · exact via sym1 fix1 (by decide +kernel) (b4_991 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_3173 theta)
    · exact b4_2731 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_113 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1105 theta)
    · exact b4_3149 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_2477 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_57 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_1597 theta)
    · exact b4_3150 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_1664 theta)
    · exact b4_3158 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_1662 theta)
    · exact b4_3155 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_2371 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2370 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2351 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_147 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2102 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2103 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_2101 theta)
    · exact b4_3151 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_306 theta)
    · exact b4_3159 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2709 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_897 theta)
    · exact b4_3146 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_139 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_339 theta)
    · exact b4_3152 theta
    · exact via sym5 fix5 (by decide +kernel) (b4_2621 theta)
    · exact via sym4 fix4 (by decide +kernel) (b4_2619 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_711 theta)
    · exact via sym6 fix6 (by decide +kernel) (b4_827 theta)
    · exact b4_10 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_826 theta)
    · exact via sym1 fix1 (by decide +kernel) (b4_710 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_813 theta)
    · exact b4_3156 theta
    · exact via sym3 fix3 (by decide +kernel) (b4_2788 theta)
    · exact via sym5 fix5 (by decide +kernel) (b4_1107 theta)
    · exact via sym3 fix3 (by decide +kernel) (b4_119 theta)
    · exact b4_3153 theta
theorem b3_3456 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_3456 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_3456 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xf0f0f0f0,0x0,0xffff0000] (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons pc1w75 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 (PetersenWireProjection.cons pc1w71 rfl)))))))) (by decide +kernel)
end Orbits1020Cost12
