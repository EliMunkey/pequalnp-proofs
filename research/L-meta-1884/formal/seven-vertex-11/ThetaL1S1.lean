import ThetaAlias
import ThetaL2S0
import ThetaL2S1
import ThetaL2S6
import ThetaL2S7
import ThetaL2S8
import ThetaL2S9
import ThetaL2S12
import ThetaL2S13
import ThetaL2S14
import ThetaL2S15
import ThetaL2S16
import ThetaL2S17
import ThetaL2S18
import ThetaL2S20
import ThetaL2S21
import ThetaL2S22
import ThetaL2S23
import ThetaL2S24
import ThetaL2S26
import ThetaL2S27
import ThetaL2S28
import ThetaL2S29
import ThetaL2S30
import ThetaL2S31
import ThetaL2S32
import ThetaL2S33
import ThetaL2S34
import ThetaL2S35
import ThetaL2S36
import ThetaL2S37
import ThetaL2S38
import ThetaL2S39
import ThetaL2S40
import ThetaL2S41
import ThetaL2S42
import ThetaL2S43
open PetersenPackedPin PetersenLayerCheck Petersen191Symmetry PetersenSymmetry
open Deleted191Cost10
namespace ThetaCert
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem b1_24 : Blocked tgt 9 s1_24 := by
  apply node_sound (nxt := [s2_693,s2_631,a644,s2_849,s2_720,s2_492,a645,s2_868,s2_733,a646,a647,s2_948,s2_754,s2_753,a85,a648,a649,a650,s2_1003,s2_988,s2_760,a651,a652,s2_990,a653,a654,a655,s2_993,a656,s2_159,a657,a658,a659,s2_517,a660,a661,s2_804,a662,s2_671,s2_655,a598,s2_970,s2_825,s2_824,a663,a664,s2_676,s2_675,s2_1004,s2_989,a665,a666,a667,a668,a669,a670,a671,a672,a673,s2_203,a674,a675,a676,a677,a678,a679,a680,s2_554,s2_537,s2_12,s2_9,s2_546,a681,a682,a683,s2_567,s2_1035,a684,a685,a686,a687,a688,a689,s2_297,a690,s2_998,a691,s2_877,a692,a693,s2_991,s2_897,a694,a695,s2_994,s2_917,s2_356,s2_339,a696,a697,s2_999,a698,a699,a700,a701,a702,a703,a704,s2_992,a705,a706,a707,a708,a709,a710,a711,s2_995,a712,a713,s2_363,s2_362,a714,a715,a716,s2_1000,a717,a718,a719,s2_996,a720,s2_374,a721,s2_1001,a722,s2_408,a723,s2_1002])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_693
    · exact b2_631
    · exact via sym2 fix2 (by decide +kernel) b2_518
    · exact b2_849
    · exact b2_720
    · exact b2_492
    · exact via sym2 fix2 (by decide +kernel) b2_495
    · exact b2_868
    · exact b2_733
    · exact via sym1 fix1 (by decide +kernel) b2_179
    · exact via sym2 fix2 (by decide +kernel) b2_568
    · exact b2_948
    · exact b2_754
    · exact b2_753
    · exact via sym1 fix1 (by decide +kernel) b2_36
    · exact via sym1 fix1 (by decide +kernel) b2_37
    · exact via sym2 fix2 (by decide +kernel) b2_587
    · exact via sym2 fix2 (by decide +kernel) b2_586
    · exact b2_1003
    · exact b2_988
    · exact b2_760
    · exact via sym3 fix3 (by decide +kernel) b2_310
    · exact via sym2 fix2 (by decide +kernel) b2_538
    · exact b2_990
    · exact via sym1 fix1 (by decide +kernel) b2_772
    · exact via sym2 fix2 (by decide +kernel) b2_302
    · exact via sym3 fix3 (by decide +kernel) b2_541
    · exact b2_993
    · exact via sym1 fix1 (by decide +kernel) b2_745
    · exact b2_159
    · exact via sym3 fix3 (by decide +kernel) b2_571
    · exact via sym1 fix1 (by decide +kernel) b2_964
    · exact via sym2 fix2 (by decide +kernel) b2_694
    · exact b2_517
    · exact via sym2 fix2 (by decide +kernel) b2_634
    · exact via sym2 fix2 (by decide +kernel) b2_851
    · exact b2_804
    · exact via sym1 fix1 (by decide +kernel) b2_215
    · exact b2_671
    · exact b2_655
    · exact via sym1 fix1 (by decide +kernel) b2_1030
    · exact b2_970
    · exact b2_825
    · exact b2_824
    · exact via sym1 fix1 (by decide +kernel) b2_38
    · exact via sym1 fix1 (by decide +kernel) b2_39
    · exact b2_676
    · exact b2_675
    · exact b2_1004
    · exact b2_989
    · exact via sym2 fix2 (by decide +kernel) b2_805
    · exact via sym3 fix3 (by decide +kernel) b2_207
    · exact via sym2 fix2 (by decide +kernel) b2_656
    · exact via sym2 fix2 (by decide +kernel) b2_972
    · exact via sym3 fix3 (by decide +kernel) b2_808
    · exact via sym2 fix2 (by decide +kernel) b2_204
    · exact via sym3 fix3 (by decide +kernel) b2_659
    · exact via sym3 fix3 (by decide +kernel) b2_976
    · exact via sym1 fix1 (by decide +kernel) b2_815
    · exact b2_203
    · exact via sym1 fix1 (by decide +kernel) b2_667
    · exact via sym1 fix1 (by decide +kernel) b2_982
    · exact via sym2 fix2 (by decide +kernel) b2_777
    · exact via sym2 fix2 (by decide +kernel) b2_775
    · exact via sym2 fix2 (by decide +kernel) b2_761
    · exact via sym1 fix1 (by decide +kernel) b2_323
    · exact via sym1 fix1 (by decide +kernel) b2_318
    · exact b2_554
    · exact b2_537
    · exact b2_12
    · exact b2_9
    · exact b2_546
    · exact via sym2 fix2 (by decide +kernel) b2_734
    · exact via sym3 fix3 (by decide +kernel) b2_185
    · exact via sym3 fix3 (by decide +kernel) b2_171
    · exact b2_567
    · exact b2_1035
    · exact via sym2 fix2 (by decide +kernel) b2_950
    · exact via sym3 fix3 (by decide +kernel) b2_737
    · exact via sym2 fix2 (by decide +kernel) b2_164
    · exact via sym1 fix1 (by decide +kernel) b2_579
    · exact via sym3 fix3 (by decide +kernel) b2_955
    · exact via sym3 fix3 (by decide +kernel) b2_764
    · exact b2_297
    · exact via sym1 fix1 (by decide +kernel) b2_549
    · exact b2_998
    · exact via sym1 fix1 (by decide +kernel) b2_315
    · exact b2_877
    · exact via sym3 fix3 (by decide +kernel) b2_412
    · exact via sym1 fix1 (by decide +kernel) b2_419
    · exact b2_991
    · exact b2_897
    · exact via sym2 fix2 (by decide +kernel) b2_375
    · exact via sym1 fix1 (by decide +kernel) b2_386
    · exact b2_994
    · exact b2_917
    · exact b2_356
    · exact b2_339
    · exact via sym1 fix1 (by decide +kernel) b2_351
    · exact via sym1 fix1 (by decide +kernel) b2_1031
    · exact b2_999
    · exact via sym2 fix2 (by decide +kernel) b2_888
    · exact via sym2 fix2 (by decide +kernel) b2_887
    · exact via sym3 fix3 (by decide +kernel) b2_426
    · exact via sym3 fix3 (by decide +kernel) b2_425
    · exact via sym1 fix1 (by decide +kernel) b2_44
    · exact via sym1 fix1 (by decide +kernel) b2_45
    · exact via sym2 fix2 (by decide +kernel) b2_1007
    · exact b2_992
    · exact via sym3 fix3 (by decide +kernel) b2_908
    · exact via sym3 fix3 (by decide +kernel) b2_907
    · exact via sym2 fix2 (by decide +kernel) b2_393
    · exact via sym2 fix2 (by decide +kernel) b2_392
    · exact via sym1 fix1 (by decide +kernel) b2_42
    · exact via sym1 fix1 (by decide +kernel) b2_43
    · exact via sym3 fix3 (by decide +kernel) b2_1014
    · exact b2_995
    · exact via sym1 fix1 (by decide +kernel) b2_931
    · exact via sym1 fix1 (by decide +kernel) b2_932
    · exact b2_363
    · exact b2_362
    · exact via sym1 fix1 (by decide +kernel) b2_40
    · exact via sym1 fix1 (by decide +kernel) b2_41
    · exact via sym2 fix2 (by decide +kernel) b2_1021
    · exact b2_1000
    · exact via sym2 fix2 (by decide +kernel) b2_918
    · exact via sym2 fix2 (by decide +kernel) b2_340
    · exact via sym3 fix3 (by decide +kernel) b2_343
    · exact b2_996
    · exact via sym2 fix2 (by decide +kernel) b2_898
    · exact b2_374
    · exact via sym3 fix3 (by decide +kernel) b2_378
    · exact b2_1001
    · exact via sym3 fix3 (by decide +kernel) b2_878
    · exact b2_408
    · exact via sym2 fix2 (by decide +kernel) b2_409
    · exact b2_1002
theorem b1_25 : Blocked tgt 9 s1_25 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_25 9 _ le
  decide +kernel
theorem b1_26 : Blocked tgt 9 s1_26 := by
  apply node_sound (nxt := [s2_697,s2_638,a724,s2_856,s2_722,s2_499,a725,s2_871,s2_740,a726,a727,a728,a533,s2_958,s2_767,a729,a730,a731,a732,a733,a734,a735,s2_784,s2_783,a736,a737,a738,a739,s2_1014,s2_1009,a740,s2_174,a741,a742,a743,s2_521,a744,a745,s2_811,a746,s2_662,s2_978,a747,a748,a749,a750,a751,a752,a753,a754,s2_827,s2_826,a755,a756,s2_678,s2_677,s2_1015,s2_1010,a757,s2_210,a758,a759,a760,a761,s2_544,s2_994,a762,a763,s2_574,a764,a765,a766,a767,a768,a769,a770,a771,a772,a773,a774,s2_591,s2_590,a711,a775,a776,s2_313,a777,a778,s2_881,a779,a780,s2_1005,a781,s2_904,s2_901,a782,a783,a784,a785,s2_12,s2_10,a786,s2_921,s2_357,s2_346,a787,a788,a789,a790,a791,a792,a793,a794,s2_1011,a795,a796,a797,a798,a799,a800,s2_1024,s2_1012,a801,s2_381,a802,s2_1013,a803,a804,s2_415,a805,a806,a807,a808,s2_434,s2_433,a809,a810,a811,a812])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_697
    · exact b2_638
    · exact via sym3 fix3 (by decide +kernel) b2_521
    · exact b2_856
    · exact b2_722
    · exact b2_499
    · exact via sym3 fix3 (by decide +kernel) b2_499
    · exact b2_871
    · exact b2_740
    · exact via sym1 fix1 (by decide +kernel) b2_181
    · exact via sym2 fix2 (by decide +kernel) b2_584
    · exact via sym2 fix2 (by decide +kernel) b2_581
    · exact via sym1 fix1 (by decide +kernel) b2_1028
    · exact b2_958
    · exact b2_767
    · exact via sym3 fix3 (by decide +kernel) b2_313
    · exact via sym2 fix2 (by decide +kernel) b2_551
    · exact via sym2 fix2 (by decide +kernel) b2_1001
    · exact via sym1 fix1 (by decide +kernel) b2_774
    · exact via sym2 fix2 (by decide +kernel) b2_320
    · exact via sym3 fix3 (by decide +kernel) b2_544
    · exact via sym3 fix3 (by decide +kernel) b2_994
    · exact b2_784
    · exact b2_783
    · exact via sym1 fix1 (by decide +kernel) b2_18
    · exact via sym1 fix1 (by decide +kernel) b2_19
    · exact via sym3 fix3 (by decide +kernel) b2_591
    · exact via sym3 fix3 (by decide +kernel) b2_590
    · exact b2_1014
    · exact b2_1009
    · exact via sym1 fix1 (by decide +kernel) b2_747
    · exact b2_174
    · exact via sym3 fix3 (by decide +kernel) b2_574
    · exact via sym1 fix1 (by decide +kernel) b2_967
    · exact via sym3 fix3 (by decide +kernel) b2_697
    · exact b2_521
    · exact via sym3 fix3 (by decide +kernel) b2_638
    · exact via sym3 fix3 (by decide +kernel) b2_856
    · exact b2_811
    · exact via sym1 fix1 (by decide +kernel) b2_217
    · exact b2_662
    · exact b2_978
    · exact via sym2 fix2 (by decide +kernel) b2_817
    · exact via sym3 fix3 (by decide +kernel) b2_210
    · exact via sym2 fix2 (by decide +kernel) b2_669
    · exact via sym2 fix2 (by decide +kernel) b2_985
    · exact via sym3 fix3 (by decide +kernel) b2_811
    · exact via sym2 fix2 (by decide +kernel) b2_217
    · exact via sym3 fix3 (by decide +kernel) b2_662
    · exact via sym3 fix3 (by decide +kernel) b2_978
    · exact b2_827
    · exact b2_826
    · exact via sym1 fix1 (by decide +kernel) b2_20
    · exact via sym1 fix1 (by decide +kernel) b2_21
    · exact b2_678
    · exact b2_677
    · exact b2_1015
    · exact b2_1010
    · exact via sym1 fix1 (by decide +kernel) b2_817
    · exact b2_210
    · exact via sym1 fix1 (by decide +kernel) b2_669
    · exact via sym1 fix1 (by decide +kernel) b2_985
    · exact via sym2 fix2 (by decide +kernel) b2_774
    · exact via sym1 fix1 (by decide +kernel) b2_320
    · exact b2_544
    · exact b2_994
    · exact via sym2 fix2 (by decide +kernel) b2_747
    · exact via sym3 fix3 (by decide +kernel) b2_174
    · exact b2_574
    · exact via sym2 fix2 (by decide +kernel) b2_967
    · exact via sym3 fix3 (by decide +kernel) b2_740
    · exact via sym2 fix2 (by decide +kernel) b2_181
    · exact via sym1 fix1 (by decide +kernel) b2_584
    · exact via sym1 fix1 (by decide +kernel) b2_581
    · exact via sym2 fix2 (by decide +kernel) b2_1028
    · exact via sym3 fix3 (by decide +kernel) b2_958
    · exact via sym3 fix3 (by decide +kernel) b2_784
    · exact via sym3 fix3 (by decide +kernel) b2_783
    · exact via sym2 fix2 (by decide +kernel) b2_18
    · exact via sym2 fix2 (by decide +kernel) b2_19
    · exact b2_591
    · exact b2_590
    · exact via sym3 fix3 (by decide +kernel) b2_1014
    · exact via sym3 fix3 (by decide +kernel) b2_1009
    · exact via sym3 fix3 (by decide +kernel) b2_767
    · exact b2_313
    · exact via sym1 fix1 (by decide +kernel) b2_551
    · exact via sym1 fix1 (by decide +kernel) b2_1001
    · exact b2_881
    · exact via sym3 fix3 (by decide +kernel) b2_415
    · exact via sym1 fix1 (by decide +kernel) b2_421
    · exact b2_1005
    · exact via sym3 fix3 (by decide +kernel) b2_904
    · exact b2_904
    · exact b2_901
    · exact via sym2 fix2 (by decide +kernel) b2_389
    · exact via sym2 fix2 (by decide +kernel) b2_388
    · exact via sym1 fix1 (by decide +kernel) b2_389
    · exact via sym1 fix1 (by decide +kernel) b2_388
    · exact b2_12
    · exact b2_10
    · exact via sym1 fix1 (by decide +kernel) b2_383
    · exact b2_921
    · exact b2_357
    · exact b2_346
    · exact via sym1 fix1 (by decide +kernel) b2_353
    · exact via sym1 fix1 (by decide +kernel) b2_1032
    · exact via sym3 fix3 (by decide +kernel) b2_1011
    · exact via sym3 fix3 (by decide +kernel) b2_921
    · exact via sym2 fix2 (by decide +kernel) b2_353
    · exact via sym3 fix3 (by decide +kernel) b2_357
    · exact via sym3 fix3 (by decide +kernel) b2_346
    · exact via sym2 fix2 (by decide +kernel) b2_1032
    · exact b2_1011
    · exact via sym2 fix2 (by decide +kernel) b2_933
    · exact via sym2 fix2 (by decide +kernel) b2_934
    · exact via sym2 fix2 (by decide +kernel) b2_22
    · exact via sym2 fix2 (by decide +kernel) b2_23
    · exact via sym3 fix3 (by decide +kernel) b2_434
    · exact via sym3 fix3 (by decide +kernel) b2_433
    · exact b2_1024
    · exact b2_1012
    · exact via sym1 fix1 (by decide +kernel) b2_903
    · exact b2_381
    · exact via sym3 fix3 (by decide +kernel) b2_381
    · exact b2_1013
    · exact via sym2 fix2 (by decide +kernel) b2_383
    · exact via sym3 fix3 (by decide +kernel) b2_881
    · exact b2_415
    · exact via sym2 fix2 (by decide +kernel) b2_421
    · exact via sym3 fix3 (by decide +kernel) b2_1005
    · exact via sym1 fix1 (by decide +kernel) b2_933
    · exact via sym1 fix1 (by decide +kernel) b2_934
    · exact b2_434
    · exact b2_433
    · exact via sym1 fix1 (by decide +kernel) b2_22
    · exact via sym1 fix1 (by decide +kernel) b2_23
    · exact via sym3 fix3 (by decide +kernel) b2_1024
    · exact via sym3 fix3 (by decide +kernel) b2_1012
theorem b1_27 : Blocked tgt 9 s1_27 := by
  apply node_sound (nxt := [s2_698,s2_639,a813,s2_857,s2_723,s2_500,a814,s2_872,s2_741,a815,a816,s2_960,s2_768,a817,a818,a819,a820,a821,a822,a823,a824,a825,a826,a827,s2_786,s2_785,a828,a829,a830,a831,s2_1021,s2_1016,a832,s2_175,a833,a834,a835,s2_522,a836,a837,s2_812,a838,s2_663,s2_980,a839,a840,a841,a842,a843,a844,a845,a846,s2_829,s2_828,a847,a848,s2_680,s2_679,s2_1022,s2_1017,a849,s2_211,a850,a851,a852,a853,s2_545,s2_996,a854,a855,s2_583,s2_575,a856,a857,a858,a859,a860,a861,a862,a863,a864,a865,a866,a867,s2_593,s2_592,s2_1023,s2_1018,a868,s2_314,a869,a870,s2_884,s2_882,a871,a872,a873,s2_1006,s2_902,a874,a875,a876,a794,s2_1011,s2_914,s2_913,a877,a878,a879,a880,s2_1024,s2_1019,s2_922,s2_347,a881,s2_1020,a882,a883,a884,a885,a886,a887,a888,s2_12,s2_11,a889,a890,s2_391,s2_382,a891,a892,a893,a894,a895,a896,s2_416,a897,a898,a899,a900,a901,s2_436,s2_435,a902,a903,a904,a905])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_698
    · exact b2_639
    · exact via sym2 fix2 (by decide +kernel) b2_524
    · exact b2_857
    · exact b2_723
    · exact b2_500
    · exact via sym2 fix2 (by decide +kernel) b2_502
    · exact b2_872
    · exact b2_741
    · exact via sym1 fix1 (by decide +kernel) b2_175
    · exact via sym2 fix2 (by decide +kernel) b2_580
    · exact b2_960
    · exact b2_768
    · exact via sym3 fix3 (by decide +kernel) b2_319
    · exact via sym2 fix2 (by decide +kernel) b2_553
    · exact via sym2 fix2 (by decide +kernel) b2_550
    · exact via sym3 fix3 (by decide +kernel) b2_1031
    · exact via sym2 fix2 (by decide +kernel) b2_999
    · exact via sym1 fix1 (by decide +kernel) b2_768
    · exact via sym2 fix2 (by decide +kernel) b2_319
    · exact via sym3 fix3 (by decide +kernel) b2_553
    · exact via sym3 fix3 (by decide +kernel) b2_550
    · exact via sym2 fix2 (by decide +kernel) b2_1031
    · exact via sym3 fix3 (by decide +kernel) b2_999
    · exact b2_786
    · exact b2_785
    · exact via sym2 fix2 (by decide +kernel) b2_30
    · exact via sym2 fix2 (by decide +kernel) b2_31
    · exact via sym2 fix2 (by decide +kernel) b2_594
    · exact via sym2 fix2 (by decide +kernel) b2_595
    · exact b2_1021
    · exact b2_1016
    · exact via sym1 fix1 (by decide +kernel) b2_741
    · exact b2_175
    · exact via sym3 fix3 (by decide +kernel) b2_580
    · exact via sym1 fix1 (by decide +kernel) b2_960
    · exact via sym2 fix2 (by decide +kernel) b2_700
    · exact b2_522
    · exact via sym2 fix2 (by decide +kernel) b2_641
    · exact via sym2 fix2 (by decide +kernel) b2_859
    · exact b2_812
    · exact via sym1 fix1 (by decide +kernel) b2_211
    · exact b2_663
    · exact b2_980
    · exact via sym2 fix2 (by decide +kernel) b2_816
    · exact via sym3 fix3 (by decide +kernel) b2_216
    · exact via sym2 fix2 (by decide +kernel) b2_668
    · exact via sym2 fix2 (by decide +kernel) b2_983
    · exact via sym3 fix3 (by decide +kernel) b2_816
    · exact via sym2 fix2 (by decide +kernel) b2_216
    · exact via sym3 fix3 (by decide +kernel) b2_668
    · exact via sym3 fix3 (by decide +kernel) b2_983
    · exact b2_829
    · exact b2_828
    · exact via sym2 fix2 (by decide +kernel) b2_27
    · exact via sym2 fix2 (by decide +kernel) b2_28
    · exact b2_680
    · exact b2_679
    · exact b2_1022
    · exact b2_1017
    · exact via sym1 fix1 (by decide +kernel) b2_812
    · exact b2_211
    · exact via sym1 fix1 (by decide +kernel) b2_663
    · exact via sym1 fix1 (by decide +kernel) b2_980
    · exact via sym2 fix2 (by decide +kernel) b2_773
    · exact via sym1 fix1 (by decide +kernel) b2_314
    · exact b2_545
    · exact b2_996
    · exact via sym2 fix2 (by decide +kernel) b2_746
    · exact via sym3 fix3 (by decide +kernel) b2_180
    · exact b2_583
    · exact b2_575
    · exact via sym3 fix3 (by decide +kernel) b2_1027
    · exact via sym2 fix2 (by decide +kernel) b2_965
    · exact via sym3 fix3 (by decide +kernel) b2_746
    · exact via sym2 fix2 (by decide +kernel) b2_180
    · exact via sym1 fix1 (by decide +kernel) b2_583
    · exact via sym1 fix1 (by decide +kernel) b2_575
    · exact via sym2 fix2 (by decide +kernel) b2_1027
    · exact via sym3 fix3 (by decide +kernel) b2_965
    · exact via sym2 fix2 (by decide +kernel) b2_787
    · exact via sym2 fix2 (by decide +kernel) b2_788
    · exact via sym2 fix2 (by decide +kernel) b2_25
    · exact via sym2 fix2 (by decide +kernel) b2_26
    · exact b2_593
    · exact b2_592
    · exact b2_1023
    · exact b2_1018
    · exact via sym3 fix3 (by decide +kernel) b2_773
    · exact b2_314
    · exact via sym1 fix1 (by decide +kernel) b2_545
    · exact via sym1 fix1 (by decide +kernel) b2_996
    · exact b2_884
    · exact b2_882
    · exact via sym3 fix3 (by decide +kernel) b2_423
    · exact via sym3 fix3 (by decide +kernel) b2_420
    · exact via sym1 fix1 (by decide +kernel) b2_416
    · exact b2_1006
    · exact b2_902
    · exact via sym2 fix2 (by decide +kernel) b2_387
    · exact via sym1 fix1 (by decide +kernel) b2_391
    · exact via sym1 fix1 (by decide +kernel) b2_382
    · exact via sym2 fix2 (by decide +kernel) b2_1032
    · exact b2_1011
    · exact b2_914
    · exact b2_913
    · exact via sym2 fix2 (by decide +kernel) b2_32
    · exact via sym2 fix2 (by decide +kernel) b2_33
    · exact via sym1 fix1 (by decide +kernel) b2_436
    · exact via sym1 fix1 (by decide +kernel) b2_435
    · exact b2_1024
    · exact b2_1019
    · exact b2_922
    · exact b2_347
    · exact via sym1 fix1 (by decide +kernel) b2_347
    · exact b2_1020
    · exact via sym3 fix3 (by decide +kernel) b2_924
    · exact via sym2 fix2 (by decide +kernel) b2_924
    · exact via sym2 fix2 (by decide +kernel) b2_923
    · exact via sym2 fix2 (by decide +kernel) b2_354
    · exact via sym2 fix2 (by decide +kernel) b2_352
    · exact via sym3 fix3 (by decide +kernel) b2_354
    · exact via sym3 fix3 (by decide +kernel) b2_352
    · exact b2_12
    · exact b2_11
    · exact via sym3 fix3 (by decide +kernel) b2_348
    · exact via sym1 fix1 (by decide +kernel) b2_902
    · exact b2_391
    · exact b2_382
    · exact via sym3 fix3 (by decide +kernel) b2_387
    · exact via sym3 fix3 (by decide +kernel) b2_1032
    · exact via sym1 fix1 (by decide +kernel) b2_1011
    · exact via sym2 fix2 (by decide +kernel) b2_348
    · exact via sym1 fix1 (by decide +kernel) b2_884
    · exact via sym1 fix1 (by decide +kernel) b2_882
    · exact b2_416
    · exact via sym2 fix2 (by decide +kernel) b2_423
    · exact via sym2 fix2 (by decide +kernel) b2_420
    · exact via sym1 fix1 (by decide +kernel) b2_1006
    · exact via sym1 fix1 (by decide +kernel) b2_914
    · exact via sym1 fix1 (by decide +kernel) b2_913
    · exact b2_436
    · exact b2_435
    · exact via sym3 fix3 (by decide +kernel) b2_32
    · exact via sym3 fix3 (by decide +kernel) b2_33
    · exact via sym1 fix1 (by decide +kernel) b2_1024
    · exact via sym1 fix1 (by decide +kernel) b2_1019
end ThetaCert
