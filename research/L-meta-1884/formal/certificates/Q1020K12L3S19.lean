import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L4S1
import Q1020K12L4S2
import Q1020K12L4S3
import Q1020K12L4S4
import Q1020K12L4S6
import Q1020K12L4S7
import Q1020K12L4S8
import Q1020K12L4S12
import Q1020K12L4S13
import Q1020K12L4S14
import Q1020K12L4S15
import Q1020K12L4S16
import Q1020K12L4S17
import Q1020K12L4S18
import Q1020K12L4S25
import Q1020K12L4S26
import Q1020K12L4S27
import Q1020K12L4S36
import Q1020K12L4S45
import Q1020K12L4S46
import Q1020K12L4S47
import Q1020K12L4S49
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0


private theorem pc1w0 : PetersenPackedPin.project cycle1 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 3 stored57 stored58 rfl rfl






private theorem pc1w9 : PetersenPackedPin.project cycle1 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored57 stored63 rfl rfl
private theorem pc1w10 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl








private theorem pc3w20 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0 := PetersenWireProjection.derive 1 stored33 stored39 rfl rfl
private theorem pc3w21 : PetersenPackedPin.project cycle3 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored39 rfl rfl
private theorem pc3w19 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333333333333000000003333333300000000 : BitVec 256) = 0xfcfcfcfc := PetersenWireProjection.derive 3 pc3w20 pc3w21 rfl rfl
private theorem pc3w22 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl


private theorem pc41w23 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored90 rfl rfl






private theorem pc41w32 : PetersenPackedPin.project extra41 (0x3333333333333333333333333333333300000000000000000000000000000000 : BitVec 256) = 0x33333333333333333333333333333333 := PetersenWireProjection.derive 1 stored91 stored95 rfl rfl
private theorem pc41w34 : PetersenPackedPin.project extra41 (0x3333333300000000333333330000000033333333000000003333333300000000 : BitVec 256) = 0x33333333333333330000000000000000 := PetersenWireProjection.derive 1 stored90 stored95 rfl rfl
private theorem pc41w31 : PetersenPackedPin.project extra41 (0x3333333333333333333333333333333333333333000000003333333300000000 : BitVec 256) = 0x33333333333333333333333333333333 := PetersenWireProjection.derive 3 pc41w32 pc41w34 rfl rfl
private theorem pc41w35 : PetersenPackedPin.project extra41 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored91 stored95 rfl rfl
private theorem pc3w37 : PetersenPackedPin.project cycle3 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0xffff0000 := PetersenWireProjection.derive 1 stored34 stored39 rfl rfl
private theorem pc3w36 : PetersenPackedPin.project cycle3 (0x3333333333333333333333333333333333333333333333330000000000000000 : BitVec 256) = 0xfffff0f0 := PetersenWireProjection.derive 3 pc3w20 pc3w37 rfl rfl
private theorem pc41w38 : PetersenPackedPin.project extra41 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffffffffffffffff := PetersenWireProjection.derive 3 stored91 stored89 rfl rfl
private theorem pc41w40 : PetersenPackedPin.project extra41 (0x3333333333333333000000000000000033333333333333330000000000000000 : BitVec 256) = 0x30303030303030303030303030303030 := PetersenWireProjection.derive 1 stored89 stored95 rfl rfl
private theorem pc41w39 : PetersenPackedPin.project extra41 (0x3333333333333333333333333333333333333333333333330000000000000000 : BitVec 256) = 0x33333333333333333333333333333333 := PetersenWireProjection.derive 3 pc41w32 pc41w40 rfl rfl




private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl




private theorem pc26w50 : PetersenPackedPin.project extra26 (0x5050505050505050505050505050505050505050505050505050505050505050 : BitVec 256) = 0xff00ff00ff00ff00ff00ff00ff00ff00 := PetersenWireProjection.derive 1 stored5 stored7 rfl rfl
private theorem pc26w51 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f0000 := PetersenWireProjection.derive 2 stored0 stored6 rfl rfl
private theorem pc26w52 : PetersenPackedPin.project extra26 (0x5500550055005500550055005500550055005500550055005500550055005500 : BitVec 256) = 0xffffffff00000000ffffffff00000000 := PetersenWireProjection.derive 1 stored4 stored7 rfl rfl
private theorem pc26w53 : PetersenPackedPin.project extra26 (0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) = 0xcccccccccccccccccccccccccccccccc := PetersenWireProjection.derive 1 stored3 stored7 rfl rfl
private theorem pc26w55 : PetersenPackedPin.project extra26 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xffffffffffffffff0000000000000000 := PetersenWireProjection.derive 1 stored2 stored7 rfl rfl
private theorem pc26w54 : PetersenPackedPin.project extra26 (0x5555555500000000000000000000000055555555000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 pc26w55 stored1 rfl rfl
private theorem pc26w57 : PetersenPackedPin.project extra26 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0xffff0000ffff0000ffff0000ffff0000 := PetersenWireProjection.derive 1 stored6 stored7 rfl rfl
private theorem pc26w56 : PetersenPackedPin.project extra26 (0x5555555544444444555555554444444455555555444444445555555544444444 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 pc26w55 pc26w57 rfl rfl
private theorem pc3w58 : PetersenPackedPin.project cycle3 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 stored35 stored39 rfl rfl
private theorem pc3w60 : PetersenPackedPin.project cycle3 (0x5555555500000000555555550000000055555555000000005555555500000000 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 1 stored35 stored40 rfl rfl
private theorem pc3w61 : PetersenPackedPin.project cycle3 (0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) = 0x0 := PetersenWireProjection.derive 1 stored39 stored40 rfl rfl
private theorem pc3w59 : PetersenPackedPin.project cycle3 (0x5555555544444444555555554444444455555555444444445555555544444444 : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc3w60 pc3w61 rfl rfl
private theorem pc26w62 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w63 : PetersenPackedPin.project extra26 (0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 1 stored1 stored7 rfl rfl
private theorem pc26w64 : PetersenPackedPin.project extra26 (0x5555555555555555555555550000000055555555555555555555555500000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 pc26w63 pc26w55 rfl rfl
private theorem pc26w65 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored0 stored2 rfl rfl
private theorem pc26w66 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555500000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 1 stored0 stored7 rfl rfl
private theorem pc26w67 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555555555555000000005555555500000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 pc26w66 pc26w55 rfl rfl
private theorem pc26w68 : PetersenPackedPin.project extra26 (0x5555555555555555555555555555555555555555555555550000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 pc26w66 pc26w63 rfl rfl
private theorem pc26w69 : PetersenPackedPin.project extra26 (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored5 stored7 rfl rfl
private theorem pc26w70 : PetersenPackedPin.project extra26 (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored4 stored7 rfl rfl
private theorem pc26w71 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored3 stored7 rfl rfl
private theorem pc26w73 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored2 stored7 rfl rfl
private theorem pc26w72 : PetersenPackedPin.project extra26 (0xaaaaaaaa000000000000000000000000aaaaaaaa000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 pc26w73 stored1 rfl rfl
private theorem pc26w75 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored1 stored7 rfl rfl
private theorem pc26w74 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w75 pc26w73 rfl rfl
private theorem pc26w77 : PetersenPackedPin.project extra26 (0x8888888888888888888888888888888888888888888888888888888888888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored6 stored7 rfl rfl
private theorem pc26w76 : PetersenPackedPin.project extra26 (0xaaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888aaaaaaaa88888888 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w73 pc26w77 rfl rfl
private theorem pc26w78 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored1 stored7 rfl rfl
private theorem pc26w80 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w79 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w78 pc26w80 rfl rfl
private theorem pc26w81 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w78 pc26w73 rfl rfl
private theorem pc26w82 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored0 stored7 rfl rfl
private theorem pc26w83 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w82 pc26w75 rfl rfl
private theorem pc26w84 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w82 pc26w80 rfl rfl
private theorem pc26w86 : PetersenPackedPin.project extra26 (0x2222222222222222222222222222222222222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored6 stored7 rfl rfl
private theorem pc26w85 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa22222222222222222222222222222222 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w82 pc26w86 rfl rfl
private theorem pc26w87 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000aaaaaaaa00000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w82 pc26w73 rfl rfl
private theorem pc26w88 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w82 pc26w78 rfl rfl
theorem b3_798 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_798 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s3_798 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0x0,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0xffff0000,0xf0f0f0f0,0xf0f0f0f0] (PetersenWireProjection.cons pc1w10 (PetersenWireProjection.cons pc1w9 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons pc1w0 rfl)))))))))) (by decide +kernel)
theorem b3_799 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_799 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(1,true),(2,true))] s3_799 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfcfcfcfc,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons pc3w19 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_800 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_800 := by
  apply PetersenIndexedNode.close (bank := [a4196,s4_666,s4_655,s4_659,s4_199,a4088,a4197,s4_657,a4198,s4_747,a4199,s4_756,a4200,s4_766,a4201,s4_698,s4_626,s4_658]) (PetersenIndexedNode.reasons 256 17 420 0x612010809840083016141308018480c282612020c048404830150100a829440083015040288014040a080501020c045414830131110a828c4044202706010808c444e0c0211110808541442024908141012400830148402480124209080490820c04a0808301280824200a0004202282014000a0205040280810809210042021d0d1410074142a0a38300a82874347060150d0a828a0802a0a45848a08116028301646020c051612c8c04184a0c045040830124040a0809000420224201200090104840240410808504042021505121005404a08014100a80854142820150528200908048404c440a080504050401c180e08131103830141814100504028204302018090c0083014240218010c088480430220c040c0483012606018080c0442026260108089818c4c02406108080c0406028008018080c042a0a13110980a0022262203110a8280c0406022a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602418080c090600860441c120c01060283824180a181006040302248480c080604420230b010808921261602404908080604030250c080c0806042a0a109008c094302212010900a8280604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030250104003d0808830141c0a0c0540408381501020c06001c8301381820e04e0604202616010808e060c2c038181080907024202504020e0442022a0a8006084054101000d50400a82907022a0a383020e04e0c05040800514100e0c1000b38301410107025040141020e0450402a2245c48a88850408b8914100a88907022a22424020e05090006028004018090901000942400180907020602109030b004240030241c080c0842408381109000c09858003028003c001924248301018080c04840403012100120208480420021011090084044808018080c04541403010180a8202000823011505400145414a080018080c060004030101809410026221301800184c4406225040018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c040604060401800848006020300018100c040602212003020181200030000131220e0406020301)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym4 fix4 (by decide +kernel) (b4_1133 theta)
    · exact b4_666 theta
    · exact b4_655 theta
    · exact b4_659 theta
    · exact b4_199 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_1152 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1157 theta)
    · exact b4_657 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_272 theta)
    · exact b4_747 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_356 theta)
    · exact b4_756 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_87 theta)
    · exact b4_766 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_646 theta)
    · exact b4_698 theta
    · exact b4_626 theta
    · exact b4_658 theta
theorem b3_801 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_801 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_801 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x33333333333333333333333333333333,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w35 (PetersenWireProjection.cons pc41w31 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w23 rfl)))))))))) (by decide +kernel)
theorem b3_802 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_802 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [(false,(4,true),(2,true))] s3_802 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xfffff0f0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons pc3w36 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_803 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_803 := by
  apply PetersenIndexedNode.close (bank := [a4202,s4_667,s4_660,s4_664,s4_89,a4063,a4203,s4_662,a4204,s4_748,a4205,s4_757,a4206,s4_768,a4201,s4_698,s4_631,s4_663]) (PetersenIndexedNode.reasons 256 17 420 0x622210809840083016141308018888c282422220c0484048301511008405440083015040288014440a080511020c04420221013111084044202420230a090808c4446141211110808420221014908141012400830148402480124209080490820c04a0808301290924200a4044202282010808a4245040210910809210042021888941006202210138300840462227060108888404a080210145848a08116028301646020c051612c8c04184a0c045040830125050a0809404420224201080894144840210510808504042021404121005000210114100a00050102820140408404908021014c440a080504050401c180e08131103830141814100504028204302018090c0083014240218010c088480430220c040c0483018008018080c04420262601080a0022c4c04260108080c0406021282818084a0221011311084044a0a26221082884040c0421012a22018080c0450400b0905808a88816120309141000c0406021612018080c04282007050380858480e0a03050a0800c040602418080c090600860441c120c01060283824180a18100604030264c480c080604420230b0108099312616030b01080806040302108080c08420028081090084004202212010808a0200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030262224003d0808830141c0a0c0588888381612020c06001c8301644420e04901042026160108099110c2c06140108090702420230a0a0e04c2822101800608404c283000d30a08840507022101282020e04a0809282800524208a081000b282024a0907029280242020e049080282045c48a08090808b8924200a08107022820424020e0509000602800401809090100094240018090702060230b030b00c2c0030241c080c08c2c0838130b000c09858003028003c001924248301018080c0484040301210030a0a000842002101400148404c282018080c04541403010180884044c48210115050989050142101018080c060004030101809410026221301800184c4406225040018080c045444030101808a08016120b01151102c2406122820018080c040c0403010300212000c0806000301018100c048480018080c040604060401800848006020300018100c040602212003020181200030000212020e0406020301)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym7 fix7 (by decide +kernel) (b4_1063 theta)
    · exact b4_667 theta
    · exact b4_660 theta
    · exact b4_664 theta
    · exact b4_89 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1090 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1092 theta)
    · exact b4_662 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_277 theta)
    · exact b4_748 theta
    · exact via sym4 fix4 (by decide +kernel) (b4_360 theta)
    · exact b4_757 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_151 theta)
    · exact b4_768 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_646 theta)
    · exact b4_698 theta
    · exact b4_631 theta
    · exact b4_663 theta
theorem b3_804 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_804 := by
  intro m le c
  apply rejects_sound extra41 i7 6 tgt small41 hot41 [] s3_804 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x33333333333333333333333333333333,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffff] (PetersenWireProjection.cons pc41w35 (PetersenWireProjection.cons pc41w39 (PetersenWireProjection.cons stored96 (PetersenWireProjection.cons stored94 (PetersenWireProjection.cons stored93 (PetersenWireProjection.cons stored92 (PetersenWireProjection.cons stored90 (PetersenWireProjection.cons stored89 (PetersenWireProjection.cons stored91 (PetersenWireProjection.cons pc41w38 rfl)))))))))) (by decide +kernel)
theorem b3_805 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_805 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_805 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w50 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_806 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_806 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_806 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffff00000000ffffffff00000000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w52 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_807 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_807 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_807 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xcccccccccccccccccccccccccccccccc,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_808 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_808 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,false),(1,false))] s3_808 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xaaaaaaaaaaaaaaaa0000000000000000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_809 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_809 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_809 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffffffffffff0000000000000000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_810 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_810 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_810 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffffffffffff0000000000000000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w55 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_811 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_811 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_811 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffffffffffffffff0000ffff0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w56 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_812 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_812 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_812 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons pc3w59 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons pc3w58 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl)))))))))) (by decide +kernel)
theorem b3_813 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_813 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s3_813 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xcccccccc,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w22 (PetersenWireProjection.cons pc3w59 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b3_814 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_814 := by
  apply PetersenIndexedNode.close (bank := [a4207,a4208,s4_296,a4209,s4_676,s4_685,s4_504,a4210,a4211,s4_678,a4212,s4_680,s4_671,a4213,s4_695,s4_673,s4_627,s4_683,s4_630,s4_681,s4_584,s4_682,a4214,a4215,s4_551,s4_684,s4_677,a4216]) (PetersenIndexedNode.reasons 256 17 408 0x622210808840484046141210118888c2824222210108404420250104006d0600840441c020c014040838050102101200348404210120e008404480861e0120208404c3c02101120210700480850100a828541484045041210114040a0825010210105414840431110a828c4044202800c10808c445001921111080854144202800bc005842008380150508401202050404800210112100900048082420120208404282021010a0209080280010808a0805000280814100a020420248401080a00285040282020e00e0c07060800a9c180e0c08380282014100743450401d050a828e0c02a0a1d0d1c18054342a0a28200a82918182820460221011918084044606323010818840414102101090102820240010808908048002404121009010420214101080917104840242020e005040282045c40a080504083802420121005414484015012820850402a0215050a0805414a08224201210131102820141014100706038204c440e0c05060504014100a08108080602420024041090084004202212010808901003010180898180602030110809898042022606313009018420203010180a00248480424020e000c0406028009818080c048380424020e020020060203010a8284c4426028008898880c442a0a030101808a88806020301141002c2416022a22058480c2450400301018085848060203010a0801c140e021612038280c1428200301018094040030201812101107048404501020e0940408404018100c0884040302018112020c2c0480821011858084044808018100c0a001f000e616020e0006040302150500c080605000d1090084805414212011814003006040302383000c0806045040098900c48e0c0131209811410006040302141000c0806044840058500c2850400b0a05811210006040302030100c08060484801292084900c042524030121200060403028005c00292424840413122101084042624210112020c4c048082101189808404480813121202200130008018020e004c48030015054001c5414a0821312098905414262414052820a000c280a8002098904c4850401b1a0d892000a3634131a141004c4826241511098905440282080010a0805445000314110a0804c4828200301189800c0484801312098800c042624030121200c4c06260018140004060421201312084800604262401810848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact via sym5 fix5 (by decide +kernel) (b4_341 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1528 theta)
    · exact b4_296 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_1986 theta)
    · exact b4_676 theta
    · exact b4_685 theta
    · exact b4_504 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_1914 theta)
    · exact via sym7 fix7 (by decide +kernel) (b4_1934 theta)
    · exact b4_678 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_2082 theta)
    · exact b4_680 theta
    · exact b4_671 theta
    · exact via sym6 fix6 (by decide +kernel) (b4_259 theta)
    · exact b4_695 theta
    · exact b4_673 theta
    · exact b4_627 theta
    · exact b4_683 theta
    · exact b4_630 theta
    · exact b4_681 theta
    · exact b4_584 theta
    · exact b4_682 theta
    · exact via sym2 fix2 (by decide +kernel) (b4_564 theta)
    · exact via sym2 fix2 (by decide +kernel) (b4_563 theta)
    · exact b4_551 theta
    · exact b4_684 theta
    · exact b4_677 theta
    · exact via sym7 fix7 (by decide +kernel) (b4_71 theta)
theorem b3_815 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_815 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(1,true))] s3_815 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w63 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w62 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_816 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_816 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_816 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w63 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_817 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_817 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(1,true))] s3_817 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xffffffffffffffffaaaaaaaaaaaaaaaa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w64 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_818 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_818 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(3,true))] s3_818 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w66 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w65 rfl)))))))))) (by decide +kernel)
theorem b3_819 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_819 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_819 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w66 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_820 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_820 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(7,true),(3,true))] s3_820 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xfffffffffffffffff0f0f0f0f0f0f0f0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w67 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_821 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_821 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(1,true),(3,true))] s3_821 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0xfafafafafafafafafafafafafafafafa,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w68 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_822 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_822 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_822 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w69 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_823 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_823 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_823 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w70 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_824 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_824 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_824 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w71 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_825 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_825 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_825 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w72 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_826 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_826 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_826 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w73 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_827 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_827 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,false))] s3_827 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_828 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_828 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(2,true),(4,false))] s3_828 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w74 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_829 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_829 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_829 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_830 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_830 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_830 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w76 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b3_831 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_831 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_831 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w78 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_832 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_832 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_832 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w79 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_833 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_833 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_833 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w81 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_834 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_834 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_834 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w82 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_835 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_835 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_835 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w83 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_836 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_836 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_836 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w84 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_837 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_837 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true)),(false,(5,true),(7,true))] s3_837 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w85 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w43 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_838 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_838 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_838 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w87 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b3_839 (theta : Extra1020K12.Theta) : Blocked tgt 9 s3_839 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,true))] s3_839 9 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xf0f00000f0f00000f0f00000f0f0000,0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w51 (PetersenWireProjection.cons pc26w88 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
