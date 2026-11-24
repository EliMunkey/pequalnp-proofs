import Q1020K12L2S6Local
import Q1020K12L3S0
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S4
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S7
import Q1020K12L3S8
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S14
import Q1020K12L3S15
import Q1020K12L3S16
import Q1020K12L3S17
import Q1020K12L3S18
import Q1020K12L3S19
import Q1020K12L3S23
import Q1020K12L3S27
import Q1020K12L3S28
import Q1020K12L3S30
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S35
import Q1020K12L3S36
import Q1020K12L3S37
import Q1020K12L3S38
import Q1020K12L3S57
import Q1020K12L3S62
import Q1020K12L3S64
import Q1020K12L3S65
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S71
import Q1020K12L3S73
import Q1020K12L3S79
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S6Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_280 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_280 := by
  apply PetersenIndexedNode.close (bank := [s3_408,s3_406,a1355,a1356,a1357,s3_1517,s3_2725,s3_1518,s3_981,s3_643,a825,a1358,a1359,s3_1526,s3_3020,s3_1527,s3_1162,s3_1160,a1360,a1361,a1362,s3_1535,a1363,s3_1536,a1364,a1365,s3_350,s3_348,a1366,s3_1544,a1367,s3_1545,a1368,a1369,s3_309,s3_307,a1370,s3_1553,a1371,s3_1554,s3_1413,s3_1270,s3_264,s3_236,a1372,s3_1560,a1373,s3_1561,a1374,a1375,s3_197,s3_195,a1376,s3_1577,a1377,s3_1578,s3_21,s3_5,a807,s3_1599,s3_1593,s3_1507,a1378,s3_1495,s3_1528,s3_1508,s3_1485,s3_1497,s3_1537,s3_1509,s3_1476,s3_1498,s3_1546,s3_1510,s3_1468,s3_1499,s3_1555,s3_1511,a1379,s3_1500,s3_1562,s3_1515,a1380,s3_1505,s3_1579,s3_1516,s3_429,s3_1506,s3_1587,s3_1519,s3_1486,a1381,s3_1538,s3_1520,s3_1477,a1382,s3_1547,s3_1521,s3_1469,a1383,s3_1556,s3_1522,a1348,a1343,s3_1565,s3_1525,a1384,a1385,s3_1580,a1386,a1387,s3_1595,s3_1588,s3_1529,s3_1479,s3_1487,s3_1548,s3_1530,s3_1470,s3_1488,s3_1557,s3_1531,a1388,s3_1491,s3_1489,s3_1603,s3_1570,s3_1533,a1389,s3_1493,s3_1581,s3_1534,s3_1170,s3_1494,s3_1589,s3_1539,s3_1471,s3_1480,s3_1558,s3_1540,a1390,s3_1481,s3_1572,s3_1542,a1391,s3_1483,s3_1582,s3_1543,a1392,s3_1484,s3_1590,s3_1549,a1393,s3_1472,s3_1574,s3_1551,a1394,s3_1474,s3_1583,s3_1552,a1395,s3_1475,s3_1591,s3_1559,a1396,a1397,s3_1584,a1398,a1399,s3_1597,s3_1592,s3_1576,a1400,a1401,s3_1594]) (PetersenIndexedNode.reasons 256 17 568 0x8056b11108404420280562101185048404805731111850484448055a10108404420280544029c5414a0008014a10114100a0008055402a54100a0808016a10105414840480529888854146202805210809c1804202805318889c1804222805190808541442028050a4040a08090008050210112100900080512404121009010804fa1010a0808404804e9404121005000804e10808a0805000804f14040a0805010804d9080921004202804c8e868a0803a0a804c0a828e0c02a0a804d0e868e0c02a1a804b8a828a0802a0a804aa303050408c04804a2101191808404804b230319180840c8049a1010504084048048920205040480080481080890804800804912020908048088047908085040420280468a82890802a0280462820050402a0280470a82850402a0a8045a8200908048408044a6220504028208044141007060382080452622070602830804394100504028208042a10100c04840080422404109008400804321011090084048041a40400c0406028040930300c040602804010809898042028041130318980480c803f908080c040602803e401ec0c040602803d0a8284c442602803f401f44c440622803c8a8280c040602803b951100c040602803b141002c241602803c151102c240612803a941000c04060280398b0900c04060280390a0801c140e02803a0b0901c14060a80388a0800c0406028037401b44c4883018004a1011070283018038401bd070283818006a10104c4884048035908084c484202803512020c4c04808803610808c4c042028034920204c48480880338a82907022a0a8033282004c48262480340a8284c48280a8032a82010702280a8031a4a084c4826248031141006c683624803224a086c6826348030941004c482624802f8a8884c482a20802f0a0811712282080300a88917122822802e8a0804c482820802d81808c4c00602802d212004c482620802e018084c480602802ca1200c4c06260802ba141406040302802b2101107048404802c2141507048405802aa10100604030280299242406040302802910808c2c04202802a12424c2c04809802890808060403028027a86040604030280270a828424023028028286044240212080268a82806040302802594504060403028025141002624130280261450426240312802494100060403028023925040604030280230a08016140b028024125041614030a80228a080060403028021a1604060403028021018084a4806028022216044a48212480208180806040302801fa0e0442402120801f0989006040302802020e0406040302801e8989042402120801e400ee00749212801ca101200708404801a9080a0068420280199202200644808801b9080a006c42028018920220060480880168a82a005821018015a82020054210180178a82a005c2a0a8014a82020050a08080129c182004870608011941020044504080139c182004c706080109410200405040800e8a08200382820800d9210200344840800f8a082003c2820800c9210200304840800a8180a002806028009a120200248480800b8180a002c06028008a120200208480800689892001803018005a0e0600140301800789892001c26248004a0e0600108381800280c0a000803028001a0e0a00048382800380c0a000c03028000a0e0a00008382)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_408 theta
    · exact b3_406 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_368 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_364 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2625 theta)
    · exact b3_1517 theta
    · exact b3_2725 theta
    · exact b3_1518 theta
    · exact b3_981 theta
    · exact b3_643 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_129 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_84 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2802 theta)
    · exact b3_1526 theta
    · exact b3_3020 theta
    · exact b3_1527 theta
    · exact b3_1162 theta
    · exact b3_1160 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_327 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_325 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2426 theta)
    · exact b3_1535 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2750 theta)
    · exact b3_1536 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_427 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_425 theta)
    · exact b3_350 theta
    · exact b3_348 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2614 theta)
    · exact b3_1544 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2734 theta)
    · exact b3_1545 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1168 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1166 theta)
    · exact b3_309 theta
    · exact b3_307 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2407 theta)
    · exact b3_1553 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2752 theta)
    · exact b3_1554 theta
    · exact b3_1413 theta
    · exact b3_1270 theta
    · exact b3_264 theta
    · exact b3_236 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2887 theta)
    · exact b3_1560 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3096 theta)
    · exact b3_1561 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_613 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_611 theta)
    · exact b3_197 theta
    · exact b3_195 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2838 theta)
    · exact b3_1577 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_3069 theta)
    · exact b3_1578 theta
    · exact b3_21 theta
    · exact b3_5 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_3351 theta)
    · exact b3_1599 theta
    · exact b3_1593 theta
    · exact b3_1507 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1174 theta)
    · exact b3_1495 theta
    · exact b3_1528 theta
    · exact b3_1508 theta
    · exact b3_1485 theta
    · exact b3_1497 theta
    · exact b3_1537 theta
    · exact b3_1509 theta
    · exact b3_1476 theta
    · exact b3_1498 theta
    · exact b3_1546 theta
    · exact b3_1510 theta
    · exact b3_1468 theta
    · exact b3_1499 theta
    · exact b3_1555 theta
    · exact b3_1511 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1179 theta)
    · exact b3_1500 theta
    · exact b3_1562 theta
    · exact b3_1515 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_434 theta)
    · exact b3_1505 theta
    · exact b3_1579 theta
    · exact b3_1516 theta
    · exact b3_429 theta
    · exact b3_1506 theta
    · exact b3_1587 theta
    · exact b3_1519 theta
    · exact b3_1486 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1188 theta)
    · exact b3_1538 theta
    · exact b3_1520 theta
    · exact b3_1477 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_435 theta)
    · exact b3_1547 theta
    · exact b3_1521 theta
    · exact b3_1469 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_454 theta)
    · exact b3_1556 theta
    · exact b3_1522 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_723 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_686 theta)
    · exact b3_1565 theta
    · exact b3_1525 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1281 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1282 theta)
    · exact b3_1580 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_803 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_802 theta)
    · exact b3_1595 theta
    · exact b3_1588 theta
    · exact b3_1529 theta
    · exact b3_1479 theta
    · exact b3_1487 theta
    · exact b3_1548 theta
    · exact b3_1530 theta
    · exact b3_1470 theta
    · exact b3_1488 theta
    · exact b3_1557 theta
    · exact b3_1531 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_442 theta)
    · exact b3_1491 theta
    · exact b3_1489 theta
    · exact b3_1603 theta
    · exact b3_1570 theta
    · exact b3_1533 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_452 theta)
    · exact b3_1493 theta
    · exact b3_1581 theta
    · exact b3_1534 theta
    · exact b3_1170 theta
    · exact b3_1494 theta
    · exact b3_1589 theta
    · exact b3_1539 theta
    · exact b3_1471 theta
    · exact b3_1480 theta
    · exact b3_1558 theta
    · exact b3_1540 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1180 theta)
    · exact b3_1481 theta
    · exact b3_1572 theta
    · exact b3_1542 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1173 theta)
    · exact b3_1483 theta
    · exact b3_1582 theta
    · exact b3_1543 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_432 theta)
    · exact b3_1484 theta
    · exact b3_1590 theta
    · exact b3_1549 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_443 theta)
    · exact b3_1472 theta
    · exact b3_1574 theta
    · exact b3_1551 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_1186 theta)
    · exact b3_1474 theta
    · exact b3_1583 theta
    · exact b3_1552 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1172 theta)
    · exact b3_1475 theta
    · exact b3_1591 theta
    · exact b3_1559 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_681 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_725 theta)
    · exact b3_1584 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1292 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1291 theta)
    · exact b3_1597 theta
    · exact b3_1592 theta
    · exact b3_1576 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_661 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_792 theta)
    · exact b3_1594 theta
end Orbits1020Cost12
