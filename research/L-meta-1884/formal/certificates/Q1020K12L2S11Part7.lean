import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S2
import Q1020K12L3S3
import Q1020K12L3S9
import Q1020K12L3S10
import Q1020K12L3S11
import Q1020K12L3S12
import Q1020K12L3S13
import Q1020K12L3S14
import Q1020K12L3S20
import Q1020K12L3S22
import Q1020K12L3S23
import Q1020K12L3S25
import Q1020K12L3S26
import Q1020K12L3S27
import Q1020K12L3S28
import Q1020K12L3S29
import Q1020K12L3S32
import Q1020K12L3S33
import Q1020K12L3S39
import Q1020K12L3S43
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S47
import Q1020K12L3S48
import Q1020K12L3S49
import Q1020K12L3S50
import Q1020K12L3S51
import Q1020K12L3S55
import Q1020K12L3S56
import Q1020K12L3S57
import Q1020K12L3S58
import Q1020K12L3S59
import Q1020K12L3S60
import Q1020K12L3S61
import Q1020K12L3S62
import Q1020K12L3S66
import Q1020K12L3S67
import Q1020K12L3S68
import Q1020K12L3S69
import Q1020K12L3S72
import Q1020K12L3S73
import Q1020K12L3S75
import Q1020K12L3S76
import Q1020K12L3S78
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S11Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b2_489 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_489 := by
  apply PetersenIndexedNode.close (bank := [s3_2337,a2291,a2292,s3_3031,s3_2416,s3_2415,a2293,a2294,a2295,a2296,s3_3159,s3_3032,s3_2445,a2297,a2298,s3_3033,a2299,a2300,a2301,s3_3036,s3_2487,s3_1807,a2302,s3_3040,a2303,a2304,a2305,s3_3045,s3_2544,a2306,a2307,s3_3051,a2308,s3_456,a2309,s3_3058,s3_21,s3_14,a2310,a846,a2311,a2312,a2313,a2314,s3_3034,a2315,a2316,a2317,a2318,a2319,s3_3037,a2320,s3_1922,s3_1861,a2321,a2322,s3_3041,s3_2775,a2323,a2324,s3_3046,a2325,s3_2868,a2326,a2327,a2328,s3_3052,a2329,s3_1054,s3_865,a2330,a2331,s3_3059,a2332,a2333,a2334,a2335,a2336,a2337,a2338,s3_3035,a2339,a2340,a2341,a2342,a2343,a2344,s3_3227,s3_3038,a2345,a2346,s3_1963,s3_1962,a2347,a2348,a2349,s3_3042,s3_2850,s3_2849,a2350,a2351,a2352,a2353,s3_3305,s3_3047,a2354,a2355,a2356,a2357,a2358,s3_3333,a1359,s3_1673,s3_1644,a2248,a780,s3_3065,a2359,a2360,a2361,s3_3039,a2362,s3_1982,a2363,s3_3043,a2364,a2365,a2366,s3_3048,a2367,a2368,a2369,a2370,s3_3067,s3_3053,a2371,s3_1192,a2372,s3_3060,a2373,a2374,a2375,s3_3044,a2376,a2377,a2378,s3_3049,a2379,a2380,a2381,s3_3054,a2382,a2383,a2384,s3_3061,a2385,a2386,a2387,s3_3050,a2388,a2389,s3_2085,s3_3055,a2390,a2391,a2392,s3_3062,a2393,a2394,a2395,s3_3056,a2396,s3_1366,a2397,s3_3063,a2398,a2399,a2400,a2401,s3_3066,s3_3064]) (PetersenIndexedNode.reasons 256 17 568 0x8059402c4840442028058210118504c202805a402cd850442828057a1010840442028056a80804202a0008056210114100a0008057280814100a0208055a10104202210180549888842022101805410808c2824202805518888c2824222805390808420221018052a4040a080900080522101121009000805324041210090108051a1010a080840480509484921005202805010808a0804202805114848a0804212804f9080921004202804e8c444a0803101804e08404e0c02101804f0c444e0c02111804d88404a0802101804ca303050408c04804c2101191808404804d230319180840c804ba101050408404804a9282850404a02804a1080890804202804b128289080420a8049908085040420280488a020908028008048084045040280080490a02050402808804788404908021018046a6220504028208046141007060382080472622070602830804594100504028208044a10100c04840080442404109008400804521011090084048043a40400c04060280424020c0c04060280411080989804202804340215898084c08040908080c040602803f894140c042501803f084044c4421018040094144c442105803e884040c042101803d951100c040602803d141002c241602803e151102c240612803c941000c040602803b8b0900c040602803b0a0801c140e02803c0b0901c14060a803a8a0800c04060280232484a00e492128038a101200e08404803a2484a00e692128021a101200de840480369080a00d84202801fb222200d6480880211080a00dc420280353222200d2c88880330a82a00ca2a0a80320840600c6210180340a82a00ce2a0a80310840600c22101802f1410200ba5040802e2420200b6908080301410200be5040802d2420200b29080802b0a88a00aa2a22802a0a08200a62820802c0a88a00ae2a2280290a08200a2282080270180a009a06028026212020096848080280180a009e060280252120200928480802324848848092128022a10120088840480242484a008e92128021a10108480840480209080a00804202801fb22208480424080211080884804202801f32222007a480a801d8a82884802a0a801d08404c4c02101801e0a828c4c02a0a801c8840484802101801b24a0884804240801a9410200685040801c24a0a006e92828019941008480424080180a88884802a2280178a082005c282080190a88a00622a2280168a08084802820801581808848006028015212008c8846408016018088c8806028014a12008480424080144009e004c03018012c009084800301801121414060403028010a1011070483028011a14150704840580102101006040302800f3262406040302800e90808c2c04202800fb2624c2c06160800e1080806040302800d0840406042100800c8a02042402100800d8840442402101800c0a02006040302800b1450406040302800a9410026241302800b9450426240312800a14100060403028009125040604030280088a08016140b028009925041614030a80080a08006040302800721604060403028006818084a4806028007a16044a482124800601808060403028004c0020424021208003c0018060403028005c0028060403028002c001042402120800110d044240212080009090006040302800190d040604030280001090042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b3_2337 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_1223 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2105 theta)
    · exact b3_3031 theta
    · exact b3_2416 theta
    · exact b3_2415 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_552 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_553 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2171 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2170 theta)
    · exact b3_3159 theta
    · exact b3_3032 theta
    · exact b3_2445 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2013 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2016 theta)
    · exact b3_3033 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2450 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1985 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2000 theta)
    · exact b3_3036 theta
    · exact b3_2487 theta
    · exact b3_1807 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_1817 theta)
    · exact b3_3040 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2345 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1195 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_2121 theta)
    · exact b3_3045 theta
    · exact b3_2544 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_464 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1879 theta)
    · exact b3_3051 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2552 theta)
    · exact b3_456 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_1895 theta)
    · exact b3_3058 theta
    · exact b3_21 theta
    · exact b3_14 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_148 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_129 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_125 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2340 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2103 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_1226 theta)
    · exact b3_3034 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2560 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1924 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1864 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_487 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3361 theta)
    · exact b3_3037 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2562 theta)
    · exact b3_1922 theta
    · exact b3_1861 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_490 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3362 theta)
    · exact b3_3041 theta
    · exact b3_2775 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_868 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_983 theta)
    · exact b3_3046 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2896 theta)
    · exact b3_2868 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_1397 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1427 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1415 theta)
    · exact b3_3052 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2778 theta)
    · exact b3_1054 theta
    · exact b3_865 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_986 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_3363 theta)
    · exact b3_3059 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2436 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2435 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2167 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2166 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_539 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_540 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3162 theta)
    · exact b3_3035 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2617 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2616 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1969 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1968 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_418 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_419 theta)
    · exact b3_3227 theta
    · exact b3_3038 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2627 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_2626 theta)
    · exact b3_1963 theta
    · exact b3_1962 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_392 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_393 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3230 theta)
    · exact b3_3042 theta
    · exact b3_2850 theta
    · exact b3_2849 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1148 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1147 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_608 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_609 theta)
    · exact b3_3305 theta
    · exact b3_3047 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2919 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_2916 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1413 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_574 theta)
    · exact via sym7 fix7 (by decide +kernel) (b3_576 theta)
    · exact b3_3333 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2802 theta)
    · exact b3_1673 theta
    · exact b3_1644 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_981 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_3351 theta)
    · exact b3_3065 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2490 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_1810 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1815 theta)
    · exact b3_3039 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2452 theta)
    · exact b3_1982 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_1998 theta)
    · exact b3_3043 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2554 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_459 theta)
    · exact via sym4 fix4 (by decide +kernel) (b3_1892 theta)
    · exact b3_3048 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_2547 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_466 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1935 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1877 theta)
    · exact b3_3067 theta
    · exact b3_3053 theta
    · exact via sym3 fix3 (by decide +kernel) (b3_2347 theta)
    · exact b3_1192 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2118 theta)
    · exact b3_3060 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2458 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1990 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1992 theta)
    · exact b3_3044 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2368 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_1210 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_2096 theta)
    · exact b3_3049 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2353 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1200 theta)
    · exact via sym2 fix2 (by decide +kernel) (b3_2088 theta)
    · exact b3_3054 theta
    · exact via sym4 fix4 (by decide +kernel) (b3_2575 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_472 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1871 theta)
    · exact b3_3061 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2578 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_474 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_1869 theta)
    · exact b3_3050 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2355 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1202 theta)
    · exact b3_2085 theta
    · exact b3_3055 theta
    · exact via sym7 fix7 (by decide +kernel) (b3_2371 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_1208 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_2094 theta)
    · exact b3_3062 theta
    · exact via sym5 fix5 (by decide +kernel) (b3_2785 theta)
    · exact via sym1 fix1 (by decide +kernel) (b3_936 theta)
    · exact via sym6 fix6 (by decide +kernel) (b3_959 theta)
    · exact b3_3056 theta
    · exact via sym1 fix1 (by decide +kernel) (b3_2876 theta)
    · exact b3_1366 theta
    · exact via sym2 fix2 (by decide +kernel) (b3_1370 theta)
    · exact b3_3063 theta
    · exact via sym6 fix6 (by decide +kernel) (b3_2787 theta)
    · exact via sym5 fix5 (by decide +kernel) (b3_957 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_1097 theta)
    · exact via sym3 fix3 (by decide +kernel) (b3_938 theta)
    · exact b3_3066 theta
    · exact b3_3064 theta
end Orbits1020Cost12
