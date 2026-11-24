import Q1020K12L1S0Local
import Q1020K12L2S0
import Q1020K12L2S1
import Q1020K12L2S4
import Q1020K12L2S5
import Q1020K12L2S6
import Q1020K12L2S7
import Q1020K12L2S8
import Q1020K12L2S9
import Q1020K12L2S10
import Q1020K12L2S11
import Q1020K12L2S12
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L1S0Local
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem b1_18 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_18 := by
  apply PetersenIndexedNode.close (bank := [s2_377,a486,a487,a488,a489,s2_494,s2_392,a490,a491,s2_500,a492,a493,a494,a495,s2_399,s2_304,a496,a497,a498,a499,a500,a501,a502,a503,s2_405,s2_404,s2_403,s2_402,a504,a505,a506,a507,a508,a509,s2_524,s2_516,s2_413,a510,a511,a512,a513,s2_57,a514,a515,a516,a517,a518,a519,a520,a521,a522,a523,a524,s2_505,a525,s2_320,a526,a527,a285,s2_462,s2_451,a528,a529,a530,a531,s2_6,s2_4,a263,s2_475,a532,a533,s2_519,a534,s2_200,s2_175,a535,a536,a537,a538,a539,a540,s2_511,a541,s2_334,a542,a543,a544,a545,a546,a547,a548,a549,a550,a551,a552,a553,a554,a555,s2_525,s2_517,a556,a557,a558,a559,a560,s2_212,a561,a562,a563,a564,a565,a566,a567,a568,a569,a570,a571,a572,a573,a574,a575,a576,a577,a578,a579,a580,a581,a582,a583,a584,a585,a586,a587,a588,a589,a590,a591,a592,a593,a594,s2_342,s2_341,s2_526,s2_518,a595,a596,s2_350,a597,a598,a599,a600,a601,a238,a602,a603,a604,a605,a606,s2_520,a607,s2_269,a608,a609,a610,a611,a612,a613,a614,a615,s2_532,s2_521,a616,a617,s2_280,s2_279,a618,a619,a620,a621,a622,a623,a624,s2_523]) (PetersenIndexedNode.reasons 256 17 556 0x805ab111084044202805a210118504c202805b31111850484448059a10108404420280582484a015e9212805721012015a840480592484a016292128056210120156840480541080a014e4202805312022014a480880551080a01524202805212022014648088050a80805414a2028050210114504a2028051280814504a020804fa101054148404804e1888854146202804d9080a01344202804f1888a013a4222804c9080854144202801f40262007a210180214010454142101804b24040a0809000804aa101121009000804ba404121009010804a21010a080840480491404121005000804890808a0805000804994040a0805010804810809210042028046c0230a08050408045c0228e0c070608047c0238e0c070608044c0220a080504080430e868a0803a0a80428a828e0c02a0a80438e868e0c02a1a80420a828a0802a0a80412303050408c048040a1011918084048041a30319180840c80402101050408404803f1202050404800803e9080890804800803f9202090804808803e1080850404202803cc01e090804840803bc01d850402820803dc01e850402820803ac01d09080484080390a82890802a028038a8a0850402a0280398a82850402a0a803828a089080484080372622050402820803694100706038208037a622070602830803614100504028208035210100c0484008034a4041090084008035a1011090084048034240400c0406028033130300c040602803290809898042028033930318980480c8032108080c0406028030c018109008480802fc01780c0406028031c01880c040602802ec017109008480802cc01600c040602802b8a8284c442602802dc01684c440622802b0a8280c040602802a151100c0406028029941002c241602802a951102c2406128029141000c04060280280b0900c04060280278a0801c140e0280288b0901c14060a80270a0800c0406028025a48484c489212802521012009284048026a484a009892128024210104c4884048023108084c484202802292020c4c04808802390808c4c042028022120204c48480880204010e007e03018021401044c48030180200a82a007e2a0a801f400f44c482624801e400ee0074280a801c24a084c482624801b941006c683624801ca4a086c682634801b141004c48262480198a8884c482a2080190a08200622820801a8a88a0068282280180a0804c482820801701808c4c006028016a12004c4826208017818084c480602801621200c4c06260801521414060403028014a1011070483028015a1415070484058014210100604030280131242406040302801290808c2c04202801392424c2c04809801210808060403028010c0082003f001e800ec0070060403028011c008806040302800dc006a00330018800ac00500604030280098a82842402302800bc00584240212080090a82806040302800814504060403028007941002624130280089450426240312800714100060403028006125040604030280058a08016140b028006925041614030a80050a08006040302800421604060403028003818084a4806028004a16044a482124800301808060403028001c000842402120800089890060403028002c00100604030280000989042402120)
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_377 theta
    · exact via sym4 fix4 (by decide +kernel) (b2_216 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_357 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_356 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_536 theta)
    · exact b2_494 theta
    · exact b2_392 theta
    · exact via sym4 fix4 (by decide +kernel) (b2_338 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_340 theta)
    · exact b2_500 theta
    · exact via sym1 fix1 (by decide +kernel) (b2_392 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_338 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_340 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_500 theta)
    · exact b2_399 theta
    · exact b2_304 theta
    · exact via sym6 fix6 (by decide +kernel) (b2_308 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_513 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_377 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_216 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_357 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_356 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_536 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_494 theta)
    · exact b2_405 theta
    · exact b2_404 theta
    · exact b2_403 theta
    · exact b2_402 theta
    · exact via sym6 fix6 (by decide +kernel) (b2_15 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_16 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_364 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_365 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_362 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_363 theta)
    · exact b2_524 theta
    · exact b2_516 theta
    · exact b2_413 theta
    · exact via sym1 fix1 (by decide +kernel) (b2_57 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_326 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_507 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_413 theta)
    · exact b2_57 theta
    · exact via sym7 fix7 (by decide +kernel) (b2_326 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_507 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_381 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_353 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_218 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_497 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_416 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_328 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_324 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_61 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_533 theta)
    · exact b2_505 theta
    · exact via sym6 fix6 (by decide +kernel) (b2_419 theta)
    · exact b2_320 theta
    · exact via sym7 fix7 (by decide +kernel) (b2_63 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_508 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_462 theta)
    · exact b2_462 theta
    · exact b2_451 theta
    · exact via sym2 fix2 (by decide +kernel) (b2_196 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_190 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_196 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_190 theta)
    · exact b2_6 theta
    · exact b2_4 theta
    · exact via sym4 fix4 (by decide +kernel) (b2_188 theta)
    · exact b2_475 theta
    · exact via sym1 fix1 (by decide +kernel) (b2_269 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_274 theta)
    · exact b2_519 theta
    · exact via sym3 fix3 (by decide +kernel) (b2_459 theta)
    · exact b2_200 theta
    · exact b2_175 theta
    · exact via sym7 fix7 (by decide +kernel) (b2_195 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_537 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_520 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_401 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_307 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_307 theta)
    · exact b2_511 theta
    · exact via sym3 fix3 (by decide +kernel) (b2_394 theta)
    · exact b2_334 theta
    · exact via sym5 fix5 (by decide +kernel) (b2_337 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_502 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_416 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_61 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_328 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_324 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_533 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_505 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_426 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_425 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_13 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_14 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_361 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_360 theta)
    · exact b2_525 theta
    · exact b2_517 theta
    · exact via sym2 fix2 (by decide +kernel) (b2_417 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_60 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_323 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_510 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_380 theta)
    · exact b2_212 theta
    · exact via sym4 fix4 (by decide +kernel) (b2_354 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_496 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_394 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_334 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_337 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_502 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_381 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_218 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_353 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_497 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_426 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_425 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_13 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_14 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_361 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_360 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_525 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_517 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_380 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_212 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_354 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_496 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_417 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_60 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_323 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_510 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_419 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_63 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_320 theta)
    · exact via sym4 fix4 (by decide +kernel) (b2_508 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_427 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_428 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_7 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_8 theta)
    · exact b2_342 theta
    · exact b2_341 theta
    · exact b2_526 theta
    · exact b2_518 theta
    · exact via sym6 fix6 (by decide +kernel) (b2_383 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_215 theta)
    · exact b2_350 theta
    · exact via sym6 fix6 (by decide +kernel) (b2_499 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_383 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_215 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_350 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_499 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_188 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_459 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_200 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_175 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_195 theta)
    · exact via sym2 fix2 (by decide +kernel) (b2_537 theta)
    · exact b2_520 theta
    · exact via sym1 fix1 (by decide +kernel) (b2_475 theta)
    · exact b2_269 theta
    · exact via sym2 fix2 (by decide +kernel) (b2_274 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_519 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_485 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_484 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_280 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_279 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_11 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_12 theta)
    · exact b2_532 theta
    · exact b2_521 theta
    · exact via sym3 fix3 (by decide +kernel) (b2_485 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_484 theta)
    · exact b2_280 theta
    · exact b2_279 theta
    · exact via sym7 fix7 (by decide +kernel) (b2_11 theta)
    · exact via sym7 fix7 (by decide +kernel) (b2_12 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_532 theta)
    · exact via sym1 fix1 (by decide +kernel) (b2_521 theta)
    · exact via sym6 fix6 (by decide +kernel) (b2_461 theta)
    · exact via sym5 fix5 (by decide +kernel) (b2_187 theta)
    · exact via sym3 fix3 (by decide +kernel) (b2_187 theta)
    · exact b2_523 theta
end Orbits1020Cost12
