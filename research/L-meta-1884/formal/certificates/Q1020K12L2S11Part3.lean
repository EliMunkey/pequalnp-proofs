import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S5
import Q1020K12L3S14
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S39
import Q1020K12L3S41
import Q1020K12L3S42
import Q1020K12L3S43
import Q1020K12L3S45
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S63
import Q1020K12L3S65
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S74
import Q1020K12L3S77
import Q1020K12L3S79
import Q1020K12L3S80
import Q1020K12L3S82
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S11Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_479 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_479 := by
  apply PetersenIndexedNode.close (bank := [s3_2330,a1991,a1992,a1993,a1994,a1995,a1996,s3_3110,a1997,s3_2892,a1998,s3_213,a1999,s3_2889,a784,a1153,a2000,a2001,a2002,a2003,a2004,a2005,a2006,a2007,a2008,a2009,a2010,a2011,a2012,a2013,a2014,a2015,a2016,a2017,s3_1843,a2018,a2019,a2020,s3_3453,a2021,s3_2909,s3_2762,a2022,a2023,a2024,a2025,a2026,s3_3264,a2027,a2028,a2029,a2030,s3_604,a2031,a2032,a2033,s3_3389,a2034,s3_2894,s3_2863,s3_2864,s3_2862,s3_229,s3_230,s3_228,a2035,a2036,a2037,a2038,a2039,s3_2890,a2040,s3_2901,s3_2866,s3_250,a2041,s3_2891,a2042,a2043,a2044,a2045,a2046,a2047,a2048,a2049,a2050,a2051,a2052,a2053,a2054,a2055,a2056,a2057,a2058,a2059,a1990,s3_2873,s3_1350,a2060,s3_10,a1988,a2061,a2062,a2063,a2064,s3_1348]) (PetersenIndexedNode.reasons 256 17 510 0x200d3006142024018d404084048033920209011006638181c0c200d07030381840194901048087030120209010a020644428081c0c0c8885030280809010480880324018842030063504008405404100625010401854100a08080304017d0848703050401c0c09010e0c024041c0c1c18070302404282009011005d28201410200b87060383040178e0c07060802d94100a080b03028202c0814040908050102c0c12100a0305010141014040501048401400090105040280014040a08050102404242009011005928201410141007060383040168e0c07060504014100a081005724201210200ac282014104016050402820802a921009081005314100a0814040c8c05010401519180c8c050100a08050404808141012000a02048402400120209080480828080a080a020a8882420121014100282014102a220504028205040121009080988814100a080a08038301c10262207060283028200a0805041005103010180a00a026221311401484c4426228027818080c04a424030101809404084805010290910900a0245010018080c044c0c0301018089010c4c02404130318980480c2404018080c05004d030101809410026221311401384c4426225040018080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c05004b018080c06009426241312401304c482624802480c040602a222018080c05404083815010288890702a022501000c0406030032018080c0490110010240440122008e480a514100c040602a0801312098914504262413122820006020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018021c010a00830040801fc00fa008d00458022400f60079003b801bc00da006aa020801a2808200750039801c280820066a0208019400c48404480880071080a005b002c8015a82020054a0808018400be005ca0808014a8202004b00248011941020044504080144009e004c5040801094102003b001c800d8a0820034282080104007e003c2820800c8a082002b001480098180a00240602800c4005e002c060280088180a0021000f212000c06001c0301800600c080605000b109008482001a212010904002806040302800400c080604a02041c1280820012838241c12808006040302248480c080604480830b012020921261602404920200604030250c080c080604a080109008481430221201090282000604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800200c0806050003800140006000f00068002c000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2330 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1738 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1737 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1734 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1843 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_3453 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2909 theta)
    · exact b3_3110 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1928 theta)
    · exact b3_2892 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2649 theta)
    · exact b3_213 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2188 theta)
    · exact b3_2889 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_19 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1407 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1388 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2330 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1843 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1738 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1734 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1737 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3453 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3110 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2909 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2330 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1843 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1738 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1734 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1737 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3453 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_3110 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2909 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2330 theta)
    · exact b3_1843 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1738 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1734 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1737 theta)
    · exact b3_3453 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_3110 theta)
    · exact b3_2909 theta
    · exact b3_2762 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_604 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1789 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1766 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1778 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3389 theta)
    · exact b3_3264 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2894 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1407 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1388 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2762 theta)
    · exact b3_604 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_1789 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1766 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1778 theta)
    · exact b3_3389 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_3264 theta)
    · exact b3_2894 theta
    · exact b3_2863 theta
    · exact b3_2864 theta
    · exact b3_2862 theta
    · exact b3_229 theta
    · exact b3_230 theta
    · exact b3_228 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1796 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1795 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1794 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3348 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_3329 theta)
    · exact b3_2890 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2901 theta)
    · exact b3_2901 theta
    · exact b3_2866 theta
    · exact b3_250 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1660 theta)
    · exact b3_2891 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1928 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2892 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2649 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_213 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2188 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2889 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1928 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2892 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2649 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_213 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2188 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2889 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1928 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2892 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2649 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_213 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2188 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2889 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2873 theta)
    · exact b3_2873 theta
    · exact b3_1350 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1350 theta)
    · exact b3_10 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1348 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2866 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_250 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1660 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2891 theta)
    · exact b3_1348 theta
end Orbits1020Cost12
