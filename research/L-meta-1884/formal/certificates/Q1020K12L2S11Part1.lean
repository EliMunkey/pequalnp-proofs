import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S14
import Q1020K12L3S32
import Q1020K12L3S41
import Q1020K12L3S42
import Q1020K12L3S43
import Q1020K12L3S55
import Q1020K12L3S65
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S77
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S11Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_472 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_472 := by
  apply PetersenIndexedNode.close (bank := [s3_2329,a1897,a1898,a1899,a1900,a1901,a1902,a1903,a1904,s3_1736,s3_1735,s3_1733,a1905,a1906,a1907,s3_2877,a1908,a1147,a1909,a1910,a1911,a1912,a1913,a1914,a1915,a1916,a1917,a1918,a1919,a1920,a1921,a1922,a1923,a1924,a1925,a1926,s3_1842,a1927,a1928,a1929,a1930,a1931,s3_2907,s3_2758,a1932,s3_2757,s3_1742,s3_1741,s3_1740,a1933,a1934,a1935,s3_3257,a1936,s3_2879,s3_2760,a1937,a1938,a1939,a1940,a1941,a1942,a1943,a1944,a1945,a1946,s3_598,a1947,a1948,a1949,a1950,a1951,s3_2872,a1952,s3_1765,s3_1764,s3_1763,a1953,a1954,a1955,s3_2881,a1956,a1957,a1958,a1959,a1960,a1961,a1962,a1963,a1964,a1965,a1966,a1967,a1968,a1969,a1970,a1971,a1972,a1973,a1974,a1975,a1976,a1977,a1978,s3_2910,a1979,a1980,s3_10,s3_1348,s3_1347,a1981,a1982,a1983,a1984,a1985,s3_2902,a1986,a1987,a1988,a1989,a1990,s3_2873]) (PetersenIndexedNode.reasons 256 17 510 0x188884808620221011911084046222322210888840424042101200ee21011080a101200da8404803cc01e1084870301080884049010614130809c0c0c282503024040840442030077803b280810809006b4202401ca00e300702404401bc90110075803a401cc9011006e2404401b600d8a0801080c01ac4202901028202400108089080480024041210090104202141010808501048401400090105040280014040a08050102404242009010311128200c4044202706010808c444e0c021111080941004203006728201410200cd00658032401aa00d30068803194100a0808c0c1410230110808c8c04202230319180840c42020a08108084808141012000a02048402400120209080480828080a080a020280824200a0004202282014000a020504028081080921004203005f14100a08200bd005d802e4018a00c30060802d8a0805040988814100a080a08038301c10262207060283028200a0805040840403012100120208480420021011090084044808018080c044c0c0301018089010c4c02404130318980480c2404018080c042505030109404420226221080894144c4421051080818084203005703010180a00ad0055802a4016a00b300588029818080c045444030101808a08016120b01151102c2406122820018080c042c2403010180850400e0a07010b0901c14060a1410018080c049212018080c05080883814180a484907029012420200c0406030040018080c049011001224044014a00a2480a150500c04060221011312084045414262414050840406020301802680c040603004c8025c012a00a1004f80274012406020301494100c0406025040098884c052504131101889410006020301151100c0406022820058482c0454440b0901848a08006020301030100c040c0084800302018000c040604030121200060203018022c01120086840480212101200910047802321012008284048020400fc8404480880081080a0077003a801c8840600702101801f400f600782101801b88406006700328018c00c2005f002e801b400d60069002d8016400ae004f0026801294102004850408015400a600505040801194102003f001e800e8a0820038282080114008600402820800d8a082002f0016800a8180a00280602800d400660030060280098180a00250011212000c0600200301428280c080604840441c120c090a0a83824202a101006040302248480c080604480830b0120209212616024049202006040302108080c08420028081090084004202212010808a02006040302800600c080605000b800540026001f000e8006c00200604030228a080c0806045040098904c08a28213120189141000604030224a080c0806042820058502c0892820b0a01850a0800604030242c080c08060406021292018090b0225241092018080604030201808848006000604018100c000602030201808181042400604800200c0806050003800140006000f00068002c000006040302)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2329 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1736 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1735 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1733 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1842 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2910 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2907 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2877 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2329 theta)
    · exact b3_1736 theta
    · exact b3_1735 theta
    · exact b3_1733 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1842 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2910 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2907 theta)
    · exact b3_2877 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_10 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1348 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1347 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2329 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1842 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1736 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1733 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1735 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2910 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2877 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2907 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2329 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1842 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1736 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1733 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1735 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2910 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2877 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2907 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2329 theta)
    · exact b3_1842 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1736 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1733 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1735 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2910 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2877 theta)
    · exact b3_2907 theta
    · exact b3_2758 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2757 theta)
    · exact b3_2757 theta
    · exact b3_1742 theta
    · exact b3_1741 theta
    · exact b3_1740 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1742 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1740 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1741 theta)
    · exact b3_3257 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2879 theta)
    · exact b3_2879 theta
    · exact b3_2760 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_598 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1765 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1763 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1764 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2902 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2881 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2872 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1348 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1347 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2760 theta)
    · exact b3_598 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_1765 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1763 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1764 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2902 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2881 theta)
    · exact b3_2872 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2760 theta)
    · exact b3_1765 theta
    · exact b3_1764 theta
    · exact b3_1763 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_598 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2902 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2872 theta)
    · exact b3_2881 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2873 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2873 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2329 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1736 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1735 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1733 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1842 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2910 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2907 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2877 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_2329 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1736 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1735 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1733 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1842 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2910 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2907 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2877 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2329 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1736 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1735 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1733 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1842 theta)
    · exact b3_2910 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2907 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2877 theta)
    · exact b3_10 theta
    · exact b3_1348 theta
    · exact b3_1347 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2760 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_598 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1765 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1763 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1764 theta)
    · exact b3_2902 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2881 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2872 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1348 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1347 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2873 theta)
    · exact b3_2873 theta
end Orbits1020Cost12
