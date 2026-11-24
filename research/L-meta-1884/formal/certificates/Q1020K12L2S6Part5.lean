import Q1020K12L2S6Local
import Q1020K12L3S0
import Q1020K12L3S1
import Q1020K12L3S3
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S10
import Q1020K12L3S15
import Q1020K12L3S16
import Q1020K12L3S17
import Q1020K12L3S19
import Q1020K12L3S23
import Q1020K12L3S27
import Q1020K12L3S28
import Q1020K12L3S30
import Q1020K12L3S38
import Q1020K12L3S39
import Q1020K12L3S40
import Q1020K12L3S57
import Q1020K12L3S62
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S69
import Q1020K12L3S72
import Q1020K12L3S73
import Q1020K12L3S79
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S6Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_282 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_282 := by
  apply PetersenIndexedNode.close (bank := [s3_424,s3_422,a1449,a1450,a1451,s3_1636,s3_2732,s3_1637,s3_981,s3_660,a846,a1452,a1359,s3_1643,s3_3057,s3_1644,s3_1165,s3_1163,a1453,a1454,a1455,s3_1650,a1456,s3_1651,a1457,a1458,s3_363,s3_361,a1459,a1460,a1461,a1462,a1463,a1464,s3_324,s3_322,a1465,a1466,a1467,a1468,s3_1269,s3_1267,s3_287,s3_285,a1469,s3_1661,a1470,s3_1662,a1471,a849,s3_129,s3_79,a1472,a1473,a1474,a1475,s3_21,s3_6,a780,s3_1681,s3_1678,s3_1628,a1476,a1477,s3_1645,s3_1629,a1478,a1479,s3_1652,s3_1630,s3_1619,a1480,s3_1654,s3_1631,s3_1609,a1481,a1482,s3_1632,a1483,a1484,s3_1663,s3_1633,a1485,a1486,a1487,s3_1635,s3_431,a1488,s3_1674,s3_1638,a1489,a1490,s3_1653,a1491,s3_1620,a1492,s3_1655,s3_1639,s3_1612,s3_1610,a1493,a1494,s3_1657,s3_1640,a1495,a1496,s3_1664,s3_1641,a1443,a1431,s3_1667,a1497,a1498,s3_1679,s3_1675,a1499,s3_1622,a1500,s3_1656,s3_1646,s3_1613,a1501,s3_1658,s3_1647,a1502,a1503,s3_1665,a1504,a1505,a1506,a1507,s3_1684,a1508,s3_1649,s3_1171,a1509,s3_1676,a1510,s3_1614,s3_1623,a1511,a1512,a1513,s3_1624,a1514,a1515,a1516,s3_1625,a1517,a1518,a1519,s3_1627,a1520,a1521,a1522,s3_1615,a1523,a1524,a1525,s3_1616,a1526,a1527,a1528,s3_1618,a1529,a1530,a1531,a1532,a1533,s3_1660,s3_1271,a1534,s3_1677,a1535,a1536,a1537,a1538]) (PetersenIndexedNode.reasons 256 17 568 0x8057402b4840442028018a1011850484048058402bd8504c282801aa1010840442028055a80804202a0008055210114100a0008056280814100a0208054a10104202210180539888842022101805310808c2824202805418888c2824222805290808420221018051a4040a080900080512101121009000805224041210090108050a1010a0808404804f9484921005202804f10808a0804202805014848a0804212804e9080921004202804d8c444a0803101804d08404e0c02101804e0c444e0c02111804c88404a0802101804ba303050408c04804b2101191808404804c230319180840c804aa10105040840480499282850404a0280491080890804202804a128289080420a8048908085040420280478a020908028008047084045040280080480a02050402808804688404908021018045a6220504028208045141007060382080462622070602830804494100504028208043a10100c04840080432404109008400804421011090084048042a40400c0406028041402040c0406028040108098980420280424020d898084c0803f908080c040602803e894140c042501803e084044c442101803f094144c442105803d884040c042101803c951100c040602803c141002c241602803d151102c240612803b941000c040602803a8b0900c040602803a0a0801c140e02803b0b0901c14060a80398a0800c0406028038401bc848083018004a1011070283018039401c5070283818006a1010848084048036908090702420280363222084804240803710808848042028035b22210702480a80348a82884802a0a803408404c4c0210180350a828c4c02a0a80338840484802101803224a088480424080319410200c45040803324a0a00ca908280309410084804240802f8a88884802a22802f0a0811712282080300a88917122a22802e8a08084802820802d8180884800602802d212008c884640802e018088c880602802ca120084804240802ba141406040302802b2101107048404802c2141507048405802aa1010060403028029b262406040302802910808c2c04202802a32624c2c06160802890808060403028027884040604210080270a020424021008028084044240210180268a02006040302802594504060403028025141002624130280261450426240312802494100060403028023925040604030280230a08016140b028024125041614030a80228a080060403028021a1604060403028021018084a4806028022216044a48212480208180806040302801f90d0442402120801f1090006040302802010d0406040302801e9090042402120801e400ee00749212801ca101200708404801a9080a006842028019b0a0a00644808801b9080a006c42028018b0a0a0060c28280168a82a00582a0a8015884060054210180178a82a005c2a0a80148840600502101801294102004850408011a420200449080801394102004c50408010a420200409080800e8a88a00382a22800d8a08200342820800f8a88a003c2a22800c8a08200302820800a8180a002806028009a120200248480800b8180a002c06028008a120200208480800690902001803018005a0e0600140301800790902001c42408004a0e0600108381800280c0a0008030280018848200042120800380c0a000c030280008848200002120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_424 theta
    · exact b3_422 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_363 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_361 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2612 theta)
    · exact b3_1636 theta
    · exact b3_2732 theta
    · exact b3_1637 theta
    · exact b3_981 theta
    · exact b3_660 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_129 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_79 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2802 theta)
    · exact b3_1643 theta
    · exact b3_3057 theta
    · exact b3_1644 theta
    · exact b3_1165 theta
    · exact b3_1163 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_324 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_322 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2409 theta)
    · exact b3_1650 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2745 theta)
    · exact b3_1651 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_424 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_422 theta)
    · exact b3_363 theta
    · exact b3_361 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2612 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1636 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2732 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1637 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1165 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1163 theta)
    · exact b3_324 theta
    · exact b3_322 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2409 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1650 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2745 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1651 theta)
    · exact b3_1269 theta
    · exact b3_1267 theta
    · exact b3_287 theta
    · exact b3_285 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2911 theta)
    · exact b3_1661 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3107 theta)
    · exact b3_1662 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_981 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_660 theta)
    · exact b3_129 theta
    · exact b3_79 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2802 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1643 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3057 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1644 theta)
    · exact b3_21 theta
    · exact b3_6 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3351 theta)
    · exact b3_1681 theta
    · exact b3_1678 theta
    · exact b3_1628 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1175 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1625 theta)
    · exact b3_1645 theta
    · exact b3_1629 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1614 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1623 theta)
    · exact b3_1652 theta
    · exact b3_1630 theta
    · exact b3_1619 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1619 theta)
    · exact b3_1654 theta
    · exact b3_1631 theta
    · exact b3_1609 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1622 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1656 theta)
    · exact b3_1632 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1178 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1624 theta)
    · exact b3_1663 theta
    · exact b3_1633 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_436 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1620 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1655 theta)
    · exact b3_1635 theta
    · exact b3_431 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1627 theta)
    · exact b3_1674 theta
    · exact b3_1638 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1616 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1187 theta)
    · exact b3_1653 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1633 theta)
    · exact b3_1620 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_436 theta)
    · exact b3_1655 theta
    · exact b3_1639 theta
    · exact b3_1612 theta
    · exact b3_1610 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_453 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1684 theta)
    · exact b3_1657 theta
    · exact b3_1640 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_719 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_688 theta)
    · exact b3_1664 theta
    · exact b3_1641 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1283 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1283 theta)
    · exact b3_1667 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_800 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_799 theta)
    · exact b3_1679 theta
    · exact b3_1675 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1631 theta)
    · exact b3_1622 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1609 theta)
    · exact b3_1656 theta
    · exact b3_1646 theta
    · exact b3_1613 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1613 theta)
    · exact b3_1658 theta
    · exact b3_1647 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_441 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1615 theta)
    · exact b3_1665 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1639 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_453 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1612 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1610 theta)
    · exact b3_1684 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1657 theta)
    · exact b3_1649 theta
    · exact b3_1171 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1618 theta)
    · exact b3_1676 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1629 theta)
    · exact b3_1614 theta
    · exact b3_1623 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1652 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1632 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1178 theta)
    · exact b3_1624 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1663 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1628 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1175 theta)
    · exact b3_1625 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1645 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1635 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_431 theta)
    · exact b3_1627 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1674 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1647 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_441 theta)
    · exact b3_1615 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1665 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1638 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1187 theta)
    · exact b3_1616 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1653 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1649 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1171 theta)
    · exact b3_1618 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1676 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1640 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_688 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_719 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1664 theta)
    · exact b3_1660 theta
    · exact b3_1271 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1286 theta)
    · exact b3_1677 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_800 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_799 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1679 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1675 theta)
end Orbits1020Cost12
