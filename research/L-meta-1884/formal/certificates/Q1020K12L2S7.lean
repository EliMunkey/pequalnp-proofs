import higher.IndexedNode
import Q1020SharedSignals
import higher.WireProjection
import Q1020K12Data
import Q1020K12L3S8
import Q1020K12L3S10
import Q1020K12L3S13
import Q1020K12L3S16
import Q1020K12L3S17
import Q1020K12L3S18
import Q1020K12L3S28
import Q1020K12L3S30
import Q1020K12L3S41
import Q1020K12L3S42
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
set_option maxRecDepth 200000
set_option maxHeartbeats 0








private theorem pc26w9 : PetersenPackedPin.project extra26 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored0 stored7 rfl rfl
private theorem pc26w10 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored2 stored7 rfl rfl
private theorem pc26w8 : PetersenPackedPin.project extra26 (0xaaaaaaaa00000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc26w9 pc26w10 rfl rfl
private theorem pc26w11 : PetersenPackedPin.project extra26 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored0 stored2 rfl rfl



private theorem pc1w15 : PetersenPackedPin.project cycle1 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0x0 := PetersenWireProjection.derive 0 stored57 stored59 rfl rfl





private theorem pc1w22 : PetersenPackedPin.project cycle1 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 2 stored57 stored63 rfl rfl
private theorem pc1w23 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0xcccc := PetersenWireProjection.derive 2 stored59 stored63 rfl rfl
private theorem pc1w21 : PetersenPackedPin.project cycle1 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0xcccccccc := PetersenWireProjection.derive 3 pc1w22 pc1w23 rfl rfl








private theorem pc3w33 : PetersenPackedPin.project cycle3 (0xcccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored33 stored39 rfl rfl
private theorem pc3w34 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored35 stored39 rfl rfl
private theorem pc3w32 : PetersenPackedPin.project cycle3 (0xcccccccc00000000cccccccccccccccccccccccccccccccccccccccc : BitVec 256) = 0x0 := PetersenWireProjection.derive 3 pc3w33 pc3w34 rfl rfl
private theorem pc26w35 : PetersenPackedPin.project extra26 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored2 stored6 rfl rfl
private theorem pc26w36 : PetersenPackedPin.project extra26 (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored3 stored7 rfl rfl
private theorem pc26w37 : PetersenPackedPin.project extra26 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored1 stored6 rfl rfl
private theorem pc26w38 : PetersenPackedPin.project extra26 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored0 stored6 rfl rfl
private theorem pc26w39 : PetersenPackedPin.project extra26 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored2 stored6 rfl rfl
private theorem pc26w40 : PetersenPackedPin.project extra26 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored0 stored1 rfl rfl
private theorem pc26w41 : PetersenPackedPin.project extra26 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored1 stored6 rfl rfl
private theorem pc26w42 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored1 stored2 rfl rfl
private theorem pc26w43 : PetersenPackedPin.project extra26 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored0 stored1 rfl rfl







private theorem pc34w51 : PetersenPackedPin.project extra34 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored18 stored22 rfl rfl

private theorem pc34w54 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc : BitVec 256) = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 2 stored19 stored22 rfl rfl
private theorem pc34w53 : PetersenPackedPin.project extra34 (0xcccc000000000000cccc000000000000cccc000000000000cccc00000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 pc34w54 stored18 rfl rfl
private theorem pc34w55 : PetersenPackedPin.project extra34 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 stored17 stored22 rfl rfl
private theorem pc34w56 : PetersenPackedPin.project extra34 (0xcccc0000cccc00000000000000000000cccc0000cccc0000000000000000 : BitVec 256) = 0xaaaa0000aaaa0000aaaa0000aaaa0000 := PetersenWireProjection.derive 0 pc34w54 stored17 rfl rfl
private theorem pc34w57 : PetersenPackedPin.project extra34 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 stored16 stored22 rfl rfl
private theorem pc34w58 : PetersenPackedPin.project extra34 (0xcccc0000cccc0000cccc0000cccc00000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaaaaaaaaaa0000000000000000 := PetersenWireProjection.derive 0 pc34w54 stored16 rfl rfl
private theorem pc34w59 : PetersenPackedPin.project extra34 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xf0f00000f0f00000f0f00000f0f00000 := PetersenWireProjection.derive 0 stored17 stored18 rfl rfl
private theorem pc34w60 : PetersenPackedPin.project extra34 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f0f0f0f0f00000000000000000 := PetersenWireProjection.derive 0 stored16 stored18 rfl rfl
private theorem pc34w61 : PetersenPackedPin.project extra34 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xfafafafafafafafafafafafafafafafa := PetersenWireProjection.derive 3 stored18 stored22 rfl rfl
private theorem pc34w62 : PetersenPackedPin.project extra34 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xffff0000ffff00000000000000000000 := PetersenWireProjection.derive 0 stored16 stored17 rfl rfl
private theorem pc34w63 : PetersenPackedPin.project extra34 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) = 0xffffaaaaffffaaaaffffaaaaffffaaaa := PetersenWireProjection.derive 3 stored17 stored22 rfl rfl
private theorem pc34w64 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000 : BitVec 256) = 0xfffff0f0fffff0f0fffff0f0fffff0f0 := PetersenWireProjection.derive 3 stored17 stored18 rfl rfl
private theorem pc34w65 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc : BitVec 256) = 0xffffffffffffffffaaaaaaaaaaaaaaaa := PetersenWireProjection.derive 3 stored16 stored22 rfl rfl
private theorem pc34w66 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000 : BitVec 256) = 0xfffffffffffffffff0f0f0f0f0f0f0f0 := PetersenWireProjection.derive 3 stored16 stored18 rfl rfl
private theorem pc34w67 : PetersenPackedPin.project extra34 (0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000 : BitVec 256) = 0xffffffffffffffffffff0000ffff0000 := PetersenWireProjection.derive 3 stored16 stored17 rfl rfl







private theorem pc30w75 : PetersenPackedPin.project extra30 (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc00000000 : BitVec 256) = 0xaa00aa00aa00aa00aa00aa00aa00aa00 := PetersenWireProjection.derive 0 stored10 stored14 rfl rfl

private theorem pc30w77 : PetersenPackedPin.project extra30 (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0 : BitVec 256) = 0x0 := PetersenWireProjection.derive 2 stored11 stored13 rfl rfl
private theorem pc30w78 : PetersenPackedPin.project extra30 (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) = 0xf000f000f000f000f000f000f000f000 := PetersenWireProjection.derive 0 stored9 stored14 rfl rfl
private theorem pc30w79 : PetersenPackedPin.project extra30 (0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000 : BitVec 256) = 0xff00ff0000000000ff00ff0000000000 := PetersenWireProjection.derive 0 stored8 stored14 rfl rfl
private theorem pc30w80 : PetersenPackedPin.project extra30 (0xffffffff000000000000000000000000ffffffff000000000000000000000000 : BitVec 256) = 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 := PetersenWireProjection.derive 0 stored9 stored10 rfl rfl
private theorem pc30w81 : PetersenPackedPin.project extra30 (0xffffffff00000000ffffffff0000000000000000000000000000000000000000 : BitVec 256) = 0xaaaaaaaa00000000aaaaaaaa00000000 := PetersenWireProjection.derive 0 stored8 stored10 rfl rfl
private theorem pc30w82 : PetersenPackedPin.project extra30 (0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) = 0xffaaffaaffaaffaaffaaffaaffaaffaa := PetersenWireProjection.derive 3 stored10 stored14 rfl rfl
private theorem pc30w83 : PetersenPackedPin.project extra30 (0xffffffffffffffff000000000000000000000000000000000000000000000000 : BitVec 256) = 0xf0f0f0f000000000f0f0f0f000000000 := PetersenWireProjection.derive 0 stored8 stored9 rfl rfl
theorem b2_294 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_294 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_294 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_295 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_295 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,false),(2,false))] s2_295 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f00000000000000000,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons pc26w11 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_296 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_296 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [] s2_296 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w8 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))) (by decide +kernel)
theorem b2_297 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_297 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_297 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0xcccccccc,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w21 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored63 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w15 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl)))))))))) (by decide +kernel)
theorem b2_298 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_298 := by
  intro m le c
  apply rejects_sound cycle3 i5 6 tgt small3 hot3 [] s2_298 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0x0,0x0,0xaaaaaaaa,0xff00ff00,0xcccccccc,0xffff0000,0xf0f0f0f0] (PetersenWireProjection.cons pc3w32 (PetersenWireProjection.cons stored40 (PetersenWireProjection.cons stored39 (PetersenWireProjection.cons stored38 (PetersenWireProjection.cons stored37 (PetersenWireProjection.cons stored36 (PetersenWireProjection.cons stored35 (PetersenWireProjection.cons stored34 (PetersenWireProjection.cons stored33 rfl))))))))) (by decide +kernel)
theorem b2_299 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_299 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s2_299 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccc,0xaaaaaaaa,0x0,0xff00ff00,0x0,0x0,0xffff0000,0xf0f0f0f0,0x0] (PetersenWireProjection.cons pc1w21 (PetersenWireProjection.cons stored64 (PetersenWireProjection.cons stored62 (PetersenWireProjection.cons stored61 (PetersenWireProjection.cons stored60 (PetersenWireProjection.cons pc1w15 (PetersenWireProjection.cons stored59 (PetersenWireProjection.cons stored58 (PetersenWireProjection.cons stored57 rfl))))))))) (by decide +kernel)
theorem b2_300 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_300 := by
  apply PetersenIndexedNode.close (bank := [s3_1731,a1539,s3_1759,s3_1762,a1540,a1541,a1542,a1543,a1544,a1545,s3_1770,s3_1773,a1546,s3_1725,a1547,a1548,s3_566,a1549,s3_1780,s3_1783,s3_1739,a1550,s3_1781,s3_1787,a1551,s3_697,a1552,a1553,s3_1755,s3_1749,a1554,s3_1767,s3_1756,a1555,a1556,s3_1774,s3_1757,s3_1743,a1557,a1558,s3_1758,a1559,a1560,s3_1782,s3_1760,a1561,a1562,s3_1788,s3_1761,s3_438,a1563,a1564,a1565,a1566,s3_1750,s3_1775,a1567,s3_1744,s3_1751,a1568,a1569,a1570,s3_1752,s3_1784,a1571,a1572,s3_1753,a1573,a1574,s3_1176,s3_1754,a1575,s3_1768,s3_1745,a1576,s3_1776,s3_1769,a1577,a1578,s3_1785,s3_1771,a1579,a1580,s3_1790,s3_1772,a1581,a1582,a1583,a1584,a1585,s3_1746,s3_1786,a1586,a1587,s3_1747,a1588,a1589,a1590,s3_1748,a1591,s3_1777,a1592,a1593,s3_1791,s3_1779,s3_1285,a1594,s3_1792,a1595,a1596,a1597,a1598]) (PetersenIndexedNode.reasons 256 17 448 0x803731110840442028036a10118504c2028037b111185048444803621010840442028035280804202a0008034a10114100a0008035a80814100a0208034210104202210180331888842022101803290808c2826101803398888c282422280321080842022101803124040a08090008030a1011210090008031a404121009010803021010a0808404802f1404121005000802e90808a0805000802f94040a0805010802e1080921004202802d0c444a0803101802c88404e0c02101802d8c444e0c02111802c08404a0802101802b2303050408c04802aa101191808404802ba30319180840c802a21010504084048029120205040480080289080890804800802992020908048088028108085040420280270a020908028008026884045040280080278a020504028088026084049080210180252622050402820802494100706038208025a622070602830802414100504028208023210100c0484008022a4041090084008023a1011090084048022240400c0406028021130300c040602802090809898042028021930318980480c8020108080c040602801f094140c042501801e884044c442101801f894144c442105801e084040c042101801d151100c040602801c941002c241602801d951102c240612801c141000c040602801b0b0900c040602801a8a0801c140e02801b8b0901c14060a801a0a0800c040602801921414060403028018a1011070483028019a1415070484058018210100604030280171242406040302801690808c2c04202801792424c2c04809801610808060403028015084040604210080148a020424021008015884044240210180140a02006040302801314504060403028012941002624130280139450426240312801214100060403028011125040604030280108a08016140b028011925041614030a80100a08006040302800f2160406040302800e818084a480602800fa16044a482124800e0180806040302800d2484806020301800ca101107028301800da484907029012800c2101006020301800b1080806024200800a9202084804200800b9080884804202800a120200602030180090a828060203018008884044c48210180098a8284c48280a80080840406020301800724a0806020301800694100262213018007a4a08262203118006141000602030180050a8880602030180048a08016120b0180058a8881612030980040a08006020301800301808060206008002a12000c0806008003818080c08060280022120006020301800100c080c08030080008848006020300800180c08060203018000084800c080604)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_1731 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1729 theta)
    · exact b3_1759 theta
    · exact b3_1762 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1731 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1729 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1759 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1762 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1732 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1725 theta)
    · exact b3_1770 theta
    · exact b3_1773 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1732 theta)
    · exact b3_1725 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1770 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1773 theta)
    · exact b3_566 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_697 theta)
    · exact b3_1780 theta
    · exact b3_1783 theta
    · exact b3_1739 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_376 theta)
    · exact b3_1781 theta
    · exact b3_1787 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_566 theta)
    · exact b3_697 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1780 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1783 theta)
    · exact b3_1755 theta
    · exact b3_1749 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1749 theta)
    · exact b3_1767 theta
    · exact b3_1756 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1744 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1751 theta)
    · exact b3_1774 theta
    · exact b3_1757 theta
    · exact b3_1743 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1750 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1775 theta)
    · exact b3_1758 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1176 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1754 theta)
    · exact b3_1782 theta
    · exact b3_1760 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_451 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1753 theta)
    · exact b3_1788 theta
    · exact b3_1761 theta
    · exact b3_438 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1752 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1784 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1757 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1743 theta)
    · exact b3_1750 theta
    · exact b3_1775 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1756 theta)
    · exact b3_1744 theta
    · exact b3_1751 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1774 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1761 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_438 theta)
    · exact b3_1752 theta
    · exact b3_1784 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1760 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_451 theta)
    · exact b3_1753 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1788 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1758 theta)
    · exact b3_1176 theta
    · exact b3_1754 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1782 theta)
    · exact b3_1768 theta
    · exact b3_1745 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1745 theta)
    · exact b3_1776 theta
    · exact b3_1769 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1177 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1748 theta)
    · exact b3_1785 theta
    · exact b3_1771 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1185 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1747 theta)
    · exact b3_1790 theta
    · exact b3_1772 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_440 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1746 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1786 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1772 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_440 theta)
    · exact b3_1746 theta
    · exact b3_1786 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1771 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1185 theta)
    · exact b3_1747 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1790 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1769 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1177 theta)
    · exact b3_1748 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1785 theta)
    · exact b3_1777 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_788 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_718 theta)
    · exact b3_1791 theta
    · exact b3_1779 theta
    · exact b3_1285 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1285 theta)
    · exact b3_1792 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1777 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_718 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_788 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1791 theta)
theorem b2_301 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_301 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(6,false))] s2_301 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w35 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_302 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_302 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(0,false))] s2_302 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w37 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_303 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_303 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,false),(2,false))] s2_303 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons pc26w38 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_304 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_304 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s2_304 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w39 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_305 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_305 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,false),(2,false))] s2_305 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w40 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_306 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_306 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_306 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w41 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_307 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_307 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(6,true),(0,true))] s2_307 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w42 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
theorem b2_308 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_308 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(0,true),(2,true))] s2_308 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa] (PetersenWireProjection.cons pc26w36 (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 (PetersenWireProjection.cons pc26w43 rfl)))))))))) (by decide +kernel)
theorem b2_309 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_309 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_309 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_310 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_310 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_310 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w53 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_311 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_311 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s2_311 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa0000aaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w56 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w55 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_312 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_312 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s2_312 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaa0000aaaa0000aaaa0000aaaa0000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w56 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_313 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_313 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false))] s2_313 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w58 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_314 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_314 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(0,false))] s2_314 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaa0000000000000000,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w58 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_315 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_315 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(2,false))] s2_315 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w51 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_316 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_316 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(0,false))] s2_316 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaa0000aaaa0000aaaa0000aaaa0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w55 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_317 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_317 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,false),(6,false))] s2_317 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaa0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons pc34w57 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_318 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_318 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(2,false))] s2_318 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f00000f0f00000f0f00000f0f00000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w59 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_319 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_319 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,false),(2,false))] s2_319 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f00000000000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons pc34w60 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_320 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_320 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s2_320 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w61 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_321 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_321 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,false),(6,false))] s2_321 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff00000000000000000000,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w62 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_322 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_322 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s2_322 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_323 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_323 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(2,true))] s2_323 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xfffff0f0fffff0f0fffff0f0fffff0f0,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w64 (PetersenWireProjection.cons stored16 rfl)))))))))) (by decide +kernel)
theorem b2_324 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_324 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true))] s2_324 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w65 rfl)))))))))) (by decide +kernel)
theorem b2_325 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_325 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(6,true),(2,true))] s2_325 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xfffffffffffffffff0f0f0f0f0f0f0f0] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w66 rfl)))))))))) (by decide +kernel)
theorem b2_326 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_326 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(6,true))] s2_326 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w67 rfl)))))))))) (by decide +kernel)
theorem b2_327 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_327 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(4,true),(0,true))] s2_327 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons pc34w63 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_328 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_328 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(6,true))] s2_328 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa] (PetersenWireProjection.cons pc34w54 (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 (PetersenWireProjection.cons pc34w65 rfl))))))))) (by decide +kernel)
theorem b2_329 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_329 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(0,false))] s2_329 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xaa00aa00aa00aa00aa00aa00aa00aa00,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w75 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_330 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_330 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,false),(2,false))] s2_330 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xf000f000f000f000f000f000f000f000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w78 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_331 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_331 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(3,false))] s2_331 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff0000000000ff00ff0000000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons pc30w79 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_332 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_332 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(2,false),(0,false))] s2_332 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w80 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_333 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_333 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(0,false))] s2_333 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaa00000000aaaaaaaa00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons pc30w81 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_334 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_334 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true))] s2_334 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w82 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
theorem b2_335 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_335 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(5,false),(2,false))] s2_335 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f000000000f0f0f0f000000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons pc30w77 (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w83 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl)))))))))) (by decide +kernel)
end Orbits1020Cost12
