import ThetaAlias
import ThetaL2S0
import ThetaL2S1
import ThetaL2S2
import ThetaL2S3
import ThetaL2S4
import ThetaL2S5
import ThetaL2S6
import ThetaL2S7
import ThetaL2S8
import ThetaL2S9
import ThetaL2S10
import ThetaL2S11
import ThetaL2S12
import ThetaL2S13
import ThetaL2S14
import ThetaL2S15
import ThetaL2S16
import ThetaL2S17
import ThetaL2S18
import ThetaL2S19
import ThetaL2S20
import ThetaL2S21
import ThetaL2S22
import ThetaL2S23
import ThetaL2S24
import ThetaL2S25
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
theorem b1_0 : Blocked tgt 9 s1_0 := by
  apply node_sound (nxt := [s2_12,s2_0,a56,s2_135,s2_134,s2_73,s2_72,s2_48,s2_46,a57,s2_141,s2_830,s2_142,s2_77,s2_74,s2_36,s2_34,a58,s2_148,a59,s2_149,s2_79,s2_78,s2_25,s2_24,s2_926,s2_155,s2_935,s2_156,s2_81,s2_80,s2_18,s2_16,a60,s2_162,a61,s2_163,s2_83,s2_82,s2_15,s2_13,a62,s2_169,a63,s2_170,a64,s2_183,s2_177,s2_129,s2_115,s2_121,s2_143,s2_130,s2_109,s2_108,s2_122,s2_184,s2_150,s2_131,s2_102,s2_123,s2_157,s2_132,s2_96,s2_124,s2_164,s2_133,s2_90,s2_89,s2_125,s2_185,s2_171,s2_128,s2_126,s2_127,s2_136,s2_110,s2_116,s2_151,s2_137,s2_103,s2_117,s2_158,s2_138,s2_97,s2_118,s2_165,s2_139,s2_91,s2_119,s2_172,s2_140,s2_84,s2_120,s2_178,s2_144,s2_104,s2_111,s2_159,s2_145,s2_98,s2_112,s2_166,s2_146,s2_92,s2_113,s2_173,s2_147,s2_85,s2_114,s2_179,s2_152,s2_99,s2_105,s2_167,s2_153,s2_93,s2_106,s2_174,s2_154,s2_86,s2_107,s2_180,s2_160,s2_94,s2_100,s2_175,s2_161,s2_87,s2_101,s2_181,s2_168,s2_88,s2_95,s2_182])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_12
    · exact b2_0
    · exact via sym1 fix1 (by decide +kernel) b2_742
    · exact b2_135
    · exact b2_134
    · exact b2_73
    · exact b2_72
    · exact b2_48
    · exact b2_46
    · exact via sym1 fix1 (by decide +kernel) b2_821
    · exact b2_141
    · exact b2_830
    · exact b2_142
    · exact b2_77
    · exact b2_74
    · exact b2_36
    · exact b2_34
    · exact via sym3 fix3 (by decide +kernel) b2_778
    · exact b2_148
    · exact via sym2 fix2 (by decide +kernel) b2_790
    · exact b2_149
    · exact b2_79
    · exact b2_78
    · exact b2_25
    · exact b2_24
    · exact b2_926
    · exact b2_155
    · exact b2_935
    · exact b2_156
    · exact b2_81
    · exact b2_80
    · exact b2_18
    · exact b2_16
    · exact via sym2 fix2 (by decide +kernel) b2_905
    · exact b2_162
    · exact via sym2 fix2 (by decide +kernel) b2_938
    · exact b2_163
    · exact b2_83
    · exact b2_82
    · exact b2_15
    · exact b2_13
    · exact via sym3 fix3 (by decide +kernel) b2_885
    · exact b2_169
    · exact via sym3 fix3 (by decide +kernel) b2_940
    · exact b2_170
    · exact via sym1 fix1 (by decide +kernel) b2_961
    · exact b2_183
    · exact b2_177
    · exact b2_129
    · exact b2_115
    · exact b2_121
    · exact b2_143
    · exact b2_130
    · exact b2_109
    · exact b2_108
    · exact b2_122
    · exact b2_184
    · exact b2_150
    · exact b2_131
    · exact b2_102
    · exact b2_123
    · exact b2_157
    · exact b2_132
    · exact b2_96
    · exact b2_124
    · exact b2_164
    · exact b2_133
    · exact b2_90
    · exact b2_89
    · exact b2_125
    · exact b2_185
    · exact b2_171
    · exact b2_128
    · exact b2_126
    · exact b2_127
    · exact b2_136
    · exact b2_110
    · exact b2_116
    · exact b2_151
    · exact b2_137
    · exact b2_103
    · exact b2_117
    · exact b2_158
    · exact b2_138
    · exact b2_97
    · exact b2_118
    · exact b2_165
    · exact b2_139
    · exact b2_91
    · exact b2_119
    · exact b2_172
    · exact b2_140
    · exact b2_84
    · exact b2_120
    · exact b2_178
    · exact b2_144
    · exact b2_104
    · exact b2_111
    · exact b2_159
    · exact b2_145
    · exact b2_98
    · exact b2_112
    · exact b2_166
    · exact b2_146
    · exact b2_92
    · exact b2_113
    · exact b2_173
    · exact b2_147
    · exact b2_85
    · exact b2_114
    · exact b2_179
    · exact b2_152
    · exact b2_99
    · exact b2_105
    · exact b2_167
    · exact b2_153
    · exact b2_93
    · exact b2_106
    · exact b2_174
    · exact b2_154
    · exact b2_86
    · exact b2_107
    · exact b2_180
    · exact b2_160
    · exact b2_94
    · exact b2_100
    · exact b2_175
    · exact b2_161
    · exact b2_87
    · exact b2_101
    · exact b2_181
    · exact b2_168
    · exact b2_88
    · exact b2_95
    · exact b2_182
theorem b1_1 : Blocked tgt 9 s1_1 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s1_1 9 _ le
  decide +kernel
theorem b1_2 : Blocked tgt 9 s1_2 := by
  apply node_sound (nxt := [s2_77,s2_75,s2_64,s2_62,a65,s2_273,s2_789,s2_274,s2_187,s2_186,s2_52,s2_50,a66,s2_280,s2_831,s2_281,s2_12,s2_1,a67,s2_287,s2_286,s2_225,s2_224,s2_30,s2_29,s2_925,s2_293,s2_936,s2_294,s2_227,s2_226,a68,a69,a70,s2_300,a71,s2_301,s2_229,s2_228,a72,a73,a74,s2_308,a75,s2_309,a76,s2_323,s2_318,s2_267,s2_254,s2_260,s2_282,s2_268,s2_246,s2_261,s2_288,s2_269,a77,s2_262,s2_295,s2_270,s2_238,s2_263,s2_302,s2_271,s2_234,s2_264,s2_310,s2_272,s2_85,s2_265,s2_266,s2_322,s2_316,s2_275,s2_247,s2_255,s2_289,s2_276,a78,s2_256,s2_296,s2_277,a79,s2_257,s2_303,s2_278,a80,s2_258,s2_311,s2_279,s2_188,s2_259,s2_317,s2_283,s2_242,s2_248,s2_297,s2_284,a81,s2_249,s2_304,s2_285,a82,a83,s2_250,s2_324,s2_312,s2_253,s2_251,s2_252,s2_290,s2_239,s2_243,s2_305,s2_291,s2_235,s2_244,s2_313,s2_292,s2_230,s2_245,s2_319,s2_298,s2_236,s2_240,s2_314,s2_299,s2_231,s2_241,s2_320,s2_306,s2_307,s2_232,s2_233,s2_237,s2_321])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_77
    · exact b2_75
    · exact b2_64
    · exact b2_62
    · exact via sym1 fix1 (by decide +kernel) b2_750
    · exact b2_273
    · exact b2_789
    · exact b2_274
    · exact b2_187
    · exact b2_186
    · exact b2_52
    · exact b2_50
    · exact via sym1 fix1 (by decide +kernel) b2_820
    · exact b2_280
    · exact b2_831
    · exact b2_281
    · exact b2_12
    · exact b2_1
    · exact via sym3 fix3 (by decide +kernel) b2_769
    · exact b2_287
    · exact b2_286
    · exact b2_225
    · exact b2_224
    · exact b2_30
    · exact b2_29
    · exact b2_925
    · exact b2_293
    · exact b2_936
    · exact b2_294
    · exact b2_227
    · exact b2_226
    · exact via sym3 fix3 (by decide +kernel) b2_18
    · exact via sym3 fix3 (by decide +kernel) b2_17
    · exact via sym2 fix2 (by decide +kernel) b2_906
    · exact b2_300
    · exact via sym2 fix2 (by decide +kernel) b2_937
    · exact b2_301
    · exact b2_229
    · exact b2_228
    · exact via sym2 fix2 (by decide +kernel) b2_15
    · exact via sym2 fix2 (by decide +kernel) b2_14
    · exact via sym3 fix3 (by decide +kernel) b2_886
    · exact b2_308
    · exact via sym3 fix3 (by decide +kernel) b2_939
    · exact b2_309
    · exact via sym1 fix1 (by decide +kernel) b2_997
    · exact b2_323
    · exact b2_318
    · exact b2_267
    · exact b2_254
    · exact b2_260
    · exact b2_282
    · exact b2_268
    · exact b2_246
    · exact b2_261
    · exact b2_288
    · exact b2_269
    · exact via sym1 fix1 (by decide +kernel) b2_104
    · exact b2_262
    · exact b2_295
    · exact b2_270
    · exact b2_238
    · exact b2_263
    · exact b2_302
    · exact b2_271
    · exact b2_234
    · exact b2_264
    · exact b2_310
    · exact b2_272
    · exact b2_85
    · exact b2_265
    · exact b2_266
    · exact b2_322
    · exact b2_316
    · exact b2_275
    · exact b2_247
    · exact b2_255
    · exact b2_289
    · exact b2_276
    · exact via sym1 fix1 (by decide +kernel) b2_191
    · exact b2_256
    · exact b2_296
    · exact b2_277
    · exact via sym3 fix3 (by decide +kernel) b2_190
    · exact b2_257
    · exact b2_303
    · exact b2_278
    · exact via sym2 fix2 (by decide +kernel) b2_189
    · exact b2_258
    · exact b2_311
    · exact b2_279
    · exact b2_188
    · exact b2_259
    · exact b2_317
    · exact b2_283
    · exact b2_242
    · exact b2_248
    · exact b2_297
    · exact b2_284
    · exact via sym3 fix3 (by decide +kernel) b2_96
    · exact b2_249
    · exact b2_304
    · exact b2_285
    · exact via sym2 fix2 (by decide +kernel) b2_90
    · exact via sym2 fix2 (by decide +kernel) b2_89
    · exact b2_250
    · exact b2_324
    · exact b2_312
    · exact b2_253
    · exact b2_251
    · exact b2_252
    · exact b2_290
    · exact b2_239
    · exact b2_243
    · exact b2_305
    · exact b2_291
    · exact b2_235
    · exact b2_244
    · exact b2_313
    · exact b2_292
    · exact b2_230
    · exact b2_245
    · exact b2_319
    · exact b2_298
    · exact b2_236
    · exact b2_240
    · exact b2_314
    · exact b2_299
    · exact b2_231
    · exact b2_241
    · exact b2_320
    · exact b2_306
    · exact b2_307
    · exact b2_232
    · exact b2_233
    · exact b2_237
    · exact b2_321
theorem b1_3 : Blocked tgt 9 s1_3 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_3 9 _ le
  decide +kernel
theorem b1_4 : Blocked tgt 9 s1_4 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_4 9 _ le
  decide +kernel
theorem b1_5 : Blocked tgt 9 s1_5 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_5 9 _ le
  decide +kernel
theorem b1_6 : Blocked tgt 9 s1_6 := by
  apply node_sound (nxt := [s2_12,s2_2,s2_724,s2_470,s2_469,s2_450,s2_449,s2_440,s2_437,a84,s2_474,s2_832,s2_477,s2_873,s2_504,s2_484,s2_452,s2_451,a85,a86,a87,a88,s2_482,s2_481,a89,s2_941,a90,s2_489,s2_454,s2_453,a91,a92,a93,s2_483,a94,s2_494,a95,a96,a97,a98,a99,a100,a101,a102,a103,a104,s2_36,s2_35,a105,a106,a107,a108,s2_1025,a109,s2_503,a110,s2_468,s2_459,s2_458,s2_463,s2_505,s2_478,a111,s2_465,s2_464,s2_471,a112,a113,s2_466,s2_506,s2_490,s2_472,a114,s2_467,s2_495,a115,a116,a117,a118,a119,s2_109,s2_108,a120,a121,a122,s2_473,s2_455,s2_460,s2_485,s2_475,a123,s2_461,s2_491,s2_476,a124,s2_462,s2_496,a125,a126,a127,a128,a129,s2_192,a130,a131,s2_479,a132,s2_456,s2_492,s2_480,a133,s2_457,s2_497,a134,a135,a136,a137,a138,s2_246,a139,a140,s2_486,a141,a142,s2_498,s2_487,a143,a144,s2_499,s2_488,s2_329,a145,s2_502,s2_493,a146,a147,s2_500,a148,s2_364,a149,a150,a151,s2_398,a152,a153])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_12
    · exact b2_2
    · exact b2_724
    · exact b2_470
    · exact b2_469
    · exact b2_450
    · exact b2_449
    · exact b2_440
    · exact b2_437
    · exact via sym2 fix2 (by decide +kernel) b2_705
    · exact b2_474
    · exact b2_832
    · exact b2_477
    · exact b2_873
    · exact b2_504
    · exact b2_484
    · exact b2_452
    · exact b2_451
    · exact via sym1 fix1 (by decide +kernel) b2_36
    · exact via sym1 fix1 (by decide +kernel) b2_35
    · exact via sym2 fix2 (by decide +kernel) b2_793
    · exact via sym2 fix2 (by decide +kernel) b2_792
    · exact b2_482
    · exact b2_481
    · exact via sym1 fix1 (by decide +kernel) b2_1025
    · exact b2_941
    · exact via sym1 fix1 (by decide +kernel) b2_503
    · exact b2_489
    · exact b2_454
    · exact b2_453
    · exact via sym3 fix3 (by decide +kernel) b2_64
    · exact via sym3 fix3 (by decide +kernel) b2_63
    · exact via sym2 fix2 (by decide +kernel) b2_791
    · exact b2_483
    · exact via sym2 fix2 (by decide +kernel) b2_944
    · exact b2_494
    · exact via sym1 fix1 (by decide +kernel) b2_454
    · exact via sym1 fix1 (by decide +kernel) b2_453
    · exact via sym2 fix2 (by decide +kernel) b2_64
    · exact via sym2 fix2 (by decide +kernel) b2_63
    · exact via sym3 fix3 (by decide +kernel) b2_791
    · exact via sym1 fix1 (by decide +kernel) b2_483
    · exact via sym3 fix3 (by decide +kernel) b2_944
    · exact via sym1 fix1 (by decide +kernel) b2_494
    · exact via sym1 fix1 (by decide +kernel) b2_452
    · exact via sym1 fix1 (by decide +kernel) b2_451
    · exact b2_36
    · exact b2_35
    · exact via sym3 fix3 (by decide +kernel) b2_793
    · exact via sym3 fix3 (by decide +kernel) b2_792
    · exact via sym1 fix1 (by decide +kernel) b2_482
    · exact via sym1 fix1 (by decide +kernel) b2_481
    · exact b2_1025
    · exact via sym1 fix1 (by decide +kernel) b2_941
    · exact b2_503
    · exact via sym1 fix1 (by decide +kernel) b2_489
    · exact b2_468
    · exact b2_459
    · exact b2_458
    · exact b2_463
    · exact b2_505
    · exact b2_478
    · exact via sym2 fix2 (by decide +kernel) b2_465
    · exact b2_465
    · exact b2_464
    · exact b2_471
    · exact via sym1 fix1 (by decide +kernel) b2_109
    · exact via sym1 fix1 (by decide +kernel) b2_108
    · exact b2_466
    · exact b2_506
    · exact b2_490
    · exact b2_472
    · exact via sym3 fix3 (by decide +kernel) b2_261
    · exact b2_467
    · exact b2_495
    · exact via sym1 fix1 (by decide +kernel) b2_472
    · exact via sym2 fix2 (by decide +kernel) b2_261
    · exact via sym1 fix1 (by decide +kernel) b2_467
    · exact via sym1 fix1 (by decide +kernel) b2_495
    · exact via sym1 fix1 (by decide +kernel) b2_471
    · exact b2_109
    · exact b2_108
    · exact via sym1 fix1 (by decide +kernel) b2_466
    · exact via sym1 fix1 (by decide +kernel) b2_506
    · exact via sym1 fix1 (by decide +kernel) b2_490
    · exact b2_473
    · exact b2_455
    · exact b2_460
    · exact b2_485
    · exact b2_475
    · exact via sym1 fix1 (by decide +kernel) b2_192
    · exact b2_461
    · exact b2_491
    · exact b2_476
    · exact via sym3 fix3 (by decide +kernel) b2_196
    · exact b2_462
    · exact b2_496
    · exact via sym1 fix1 (by decide +kernel) b2_476
    · exact via sym2 fix2 (by decide +kernel) b2_196
    · exact via sym1 fix1 (by decide +kernel) b2_462
    · exact via sym1 fix1 (by decide +kernel) b2_496
    · exact via sym1 fix1 (by decide +kernel) b2_475
    · exact b2_192
    · exact via sym1 fix1 (by decide +kernel) b2_461
    · exact via sym1 fix1 (by decide +kernel) b2_491
    · exact b2_479
    · exact via sym1 fix1 (by decide +kernel) b2_246
    · exact b2_456
    · exact b2_492
    · exact b2_480
    · exact via sym3 fix3 (by decide +kernel) b2_122
    · exact b2_457
    · exact b2_497
    · exact via sym1 fix1 (by decide +kernel) b2_480
    · exact via sym2 fix2 (by decide +kernel) b2_122
    · exact via sym1 fix1 (by decide +kernel) b2_457
    · exact via sym1 fix1 (by decide +kernel) b2_497
    · exact via sym1 fix1 (by decide +kernel) b2_479
    · exact b2_246
    · exact via sym1 fix1 (by decide +kernel) b2_456
    · exact via sym1 fix1 (by decide +kernel) b2_492
    · exact b2_486
    · exact via sym3 fix3 (by decide +kernel) b2_401
    · exact via sym1 fix1 (by decide +kernel) b2_398
    · exact b2_498
    · exact b2_487
    · exact via sym2 fix2 (by decide +kernel) b2_367
    · exact via sym1 fix1 (by decide +kernel) b2_364
    · exact b2_499
    · exact b2_488
    · exact b2_329
    · exact via sym1 fix1 (by decide +kernel) b2_329
    · exact b2_502
    · exact b2_493
    · exact via sym2 fix2 (by decide +kernel) b2_332
    · exact via sym3 fix3 (by decide +kernel) b2_332
    · exact b2_500
    · exact via sym1 fix1 (by decide +kernel) b2_487
    · exact b2_364
    · exact via sym3 fix3 (by decide +kernel) b2_367
    · exact via sym1 fix1 (by decide +kernel) b2_499
    · exact via sym1 fix1 (by decide +kernel) b2_486
    · exact b2_398
    · exact via sym2 fix2 (by decide +kernel) b2_401
    · exact via sym1 fix1 (by decide +kernel) b2_498
theorem b1_7 : Blocked tgt 9 s1_7 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s1_7 9 _ le
  decide +kernel
theorem b1_8 : Blocked tgt 9 s1_8 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_8 9 _ le
  decide +kernel
theorem b1_9 : Blocked tgt 9 s1_9 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_9 9 _ le
  decide +kernel
theorem b1_10 : Blocked tgt 9 s1_10 := by
  apply node_sound (nxt := [s2_12,s2_3,s2_699,s2_608,s2_607,s2_858,s2_642,s2_619,s2_598,s2_596,s2_440,s2_438,a154,s2_616,a155,s2_622,s2_600,s2_599,a156,a157,a158,s2_617,s2_942,s2_628,s2_602,s2_601,a159,a160,a161,s2_618,a162,s2_633,a163,a164,a165,a166,a167,a168,a169,a170,a171,a172,s2_48,s2_47,a173,a174,a175,a176,a177,a178,a179,s2_609,s2_459,s2_458,a180,s2_644,s2_623,s2_610,a181,a182,s2_629,s2_611,a183,a184,s2_634,a185,a186,a187,a188,a189,s2_115,a190,a191,s2_613,s2_612,s2_507,s2_604,s2_603,s2_624,s2_614,a192,a193,s2_605,s2_643,s2_630,s2_615,a194,s2_606,s2_635,a195,a196,a197,a198,a199,s2_194,s2_193,a200,a201,a202,s2_620,a203,s2_529,s2_631,s2_621,a204,s2_559,s2_636,a205,a206,a207,a208,a209,s2_254,a210,a211,s2_625,a212,a213,s2_637,s2_626,a214,a215,s2_638,s2_627,s2_330,a216,s2_641,s2_632,a217,a218,s2_639,a219,s2_365,a220,a221,a222,s2_399,a223,a224])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_12
    · exact b2_3
    · exact b2_699
    · exact b2_608
    · exact b2_607
    · exact b2_858
    · exact b2_642
    · exact b2_619
    · exact b2_598
    · exact b2_596
    · exact b2_440
    · exact b2_438
    · exact via sym2 fix2 (by decide +kernel) b2_704
    · exact b2_616
    · exact via sym2 fix2 (by decide +kernel) b2_794
    · exact b2_622
    · exact b2_600
    · exact b2_599
    · exact via sym1 fix1 (by decide +kernel) b2_48
    · exact via sym1 fix1 (by decide +kernel) b2_47
    · exact via sym2 fix2 (by decide +kernel) b2_834
    · exact b2_617
    · exact b2_942
    · exact b2_628
    · exact b2_602
    · exact b2_601
    · exact via sym3 fix3 (by decide +kernel) b2_52
    · exact via sym3 fix3 (by decide +kernel) b2_51
    · exact via sym2 fix2 (by decide +kernel) b2_833
    · exact b2_618
    · exact via sym2 fix2 (by decide +kernel) b2_943
    · exact b2_633
    · exact via sym1 fix1 (by decide +kernel) b2_602
    · exact via sym1 fix1 (by decide +kernel) b2_601
    · exact via sym2 fix2 (by decide +kernel) b2_52
    · exact via sym2 fix2 (by decide +kernel) b2_51
    · exact via sym3 fix3 (by decide +kernel) b2_833
    · exact via sym1 fix1 (by decide +kernel) b2_618
    · exact via sym3 fix3 (by decide +kernel) b2_943
    · exact via sym1 fix1 (by decide +kernel) b2_633
    · exact via sym1 fix1 (by decide +kernel) b2_600
    · exact via sym1 fix1 (by decide +kernel) b2_599
    · exact b2_48
    · exact b2_47
    · exact via sym3 fix3 (by decide +kernel) b2_834
    · exact via sym1 fix1 (by decide +kernel) b2_617
    · exact via sym1 fix1 (by decide +kernel) b2_942
    · exact via sym1 fix1 (by decide +kernel) b2_628
    · exact via sym2 fix2 (by decide +kernel) b2_509
    · exact via sym2 fix2 (by decide +kernel) b2_510
    · exact via sym2 fix2 (by decide +kernel) b2_508
    · exact b2_609
    · exact b2_459
    · exact b2_458
    · exact via sym2 fix2 (by decide +kernel) b2_460
    · exact b2_644
    · exact b2_623
    · exact b2_610
    · exact via sym1 fix1 (by decide +kernel) b2_115
    · exact via sym2 fix2 (by decide +kernel) b2_560
    · exact b2_629
    · exact b2_611
    · exact via sym3 fix3 (by decide +kernel) b2_255
    · exact via sym2 fix2 (by decide +kernel) b2_530
    · exact b2_634
    · exact via sym1 fix1 (by decide +kernel) b2_611
    · exact via sym2 fix2 (by decide +kernel) b2_255
    · exact via sym3 fix3 (by decide +kernel) b2_530
    · exact via sym1 fix1 (by decide +kernel) b2_634
    · exact via sym1 fix1 (by decide +kernel) b2_610
    · exact b2_115
    · exact via sym3 fix3 (by decide +kernel) b2_560
    · exact via sym1 fix1 (by decide +kernel) b2_629
    · exact b2_613
    · exact b2_612
    · exact b2_507
    · exact b2_604
    · exact b2_603
    · exact b2_624
    · exact b2_614
    · exact via sym1 fix1 (by decide +kernel) b2_194
    · exact via sym1 fix1 (by decide +kernel) b2_193
    · exact b2_605
    · exact b2_643
    · exact b2_630
    · exact b2_615
    · exact via sym3 fix3 (by decide +kernel) b2_195
    · exact b2_606
    · exact b2_635
    · exact via sym1 fix1 (by decide +kernel) b2_615
    · exact via sym2 fix2 (by decide +kernel) b2_195
    · exact via sym1 fix1 (by decide +kernel) b2_606
    · exact via sym1 fix1 (by decide +kernel) b2_635
    · exact via sym1 fix1 (by decide +kernel) b2_614
    · exact b2_194
    · exact b2_193
    · exact via sym1 fix1 (by decide +kernel) b2_605
    · exact via sym1 fix1 (by decide +kernel) b2_643
    · exact via sym1 fix1 (by decide +kernel) b2_630
    · exact b2_620
    · exact via sym1 fix1 (by decide +kernel) b2_254
    · exact b2_529
    · exact b2_631
    · exact b2_621
    · exact via sym3 fix3 (by decide +kernel) b2_116
    · exact b2_559
    · exact b2_636
    · exact via sym1 fix1 (by decide +kernel) b2_621
    · exact via sym2 fix2 (by decide +kernel) b2_116
    · exact via sym1 fix1 (by decide +kernel) b2_559
    · exact via sym1 fix1 (by decide +kernel) b2_636
    · exact via sym1 fix1 (by decide +kernel) b2_620
    · exact b2_254
    · exact via sym1 fix1 (by decide +kernel) b2_529
    · exact via sym1 fix1 (by decide +kernel) b2_631
    · exact b2_625
    · exact via sym3 fix3 (by decide +kernel) b2_400
    · exact via sym1 fix1 (by decide +kernel) b2_399
    · exact b2_637
    · exact b2_626
    · exact via sym2 fix2 (by decide +kernel) b2_366
    · exact via sym1 fix1 (by decide +kernel) b2_365
    · exact b2_638
    · exact b2_627
    · exact b2_330
    · exact via sym1 fix1 (by decide +kernel) b2_330
    · exact b2_641
    · exact b2_632
    · exact via sym2 fix2 (by decide +kernel) b2_331
    · exact via sym3 fix3 (by decide +kernel) b2_331
    · exact b2_639
    · exact via sym1 fix1 (by decide +kernel) b2_626
    · exact b2_365
    · exact via sym3 fix3 (by decide +kernel) b2_366
    · exact via sym1 fix1 (by decide +kernel) b2_638
    · exact via sym1 fix1 (by decide +kernel) b2_625
    · exact b2_399
    · exact via sym2 fix2 (by decide +kernel) b2_400
    · exact via sym1 fix1 (by decide +kernel) b2_637
theorem b1_11 : Blocked tgt 9 s1_11 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_11 9 _ le
  decide +kernel
theorem b1_12 : Blocked tgt 9 s1_12 := by
  intro m le c
  apply rejects_sound hex8 i6 7 tgt small8 hot8 [] s1_12 9 _ le
  decide +kernel
theorem b1_13 : Blocked tgt 9 s1_13 := by
  apply node_sound (nxt := [s2_12,s2_4,s2_501,s2_470,s2_469,s2_686,s2_685,s2_598,s2_597,s2_682,s2_681,s2_835,s2_711,a225,a226,a227,s2_707,s2_706,a228,a229,s2_684,s2_683,s2_945,s2_717,a230,a231,a232,a233,a234,a235,a236,a237,a238,a239,a240,a241,a242,a243,a244,a245,a246,a247,s2_77,s2_76,a248,a249,a250,a251,s2_687,s2_609,a252,s2_712,a253,s2_725,s2_713,s2_708,a254,a255,s2_718,s2_709,a256,a257,a258,a259,a260,a261,a262,a263,s2_130,a264,a265,a266,s2_511,a267,a268,s2_710,a269,s2_649,s2_719,a270,a271,a272,a273,a274,a275,a276,a277,a278,s2_197,a279,a280,a281,a282,s2_531,s2_720,a283,a284,s2_561,a285,a286,a287,a288,a289,a290,s2_268,a291,a292,s2_714,a293,a294,s2_721,s2_715,a295,a296,s2_722,s2_716,s2_333,a297,a298,a299,a300,a301,s2_723,a302,s2_368,a303,a304,a305,s2_402,a306,a307])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_12
    · exact b2_4
    · exact b2_501
    · exact b2_470
    · exact b2_469
    · exact b2_686
    · exact b2_685
    · exact b2_598
    · exact b2_597
    · exact b2_682
    · exact b2_681
    · exact b2_835
    · exact b2_711
    · exact via sym2 fix2 (by decide +kernel) b2_501
    · exact via sym2 fix2 (by decide +kernel) b2_470
    · exact via sym2 fix2 (by decide +kernel) b2_469
    · exact b2_707
    · exact b2_706
    · exact via sym1 fix1 (by decide +kernel) b2_77
    · exact via sym1 fix1 (by decide +kernel) b2_76
    · exact b2_684
    · exact b2_683
    · exact b2_945
    · exact b2_717
    · exact via sym2 fix2 (by decide +kernel) b2_707
    · exact via sym2 fix2 (by decide +kernel) b2_706
    · exact via sym3 fix3 (by decide +kernel) b2_77
    · exact via sym3 fix3 (by decide +kernel) b2_76
    · exact via sym2 fix2 (by decide +kernel) b2_684
    · exact via sym2 fix2 (by decide +kernel) b2_683
    · exact via sym2 fix2 (by decide +kernel) b2_945
    · exact via sym2 fix2 (by decide +kernel) b2_717
    · exact via sym3 fix3 (by decide +kernel) b2_707
    · exact via sym3 fix3 (by decide +kernel) b2_706
    · exact via sym2 fix2 (by decide +kernel) b2_77
    · exact via sym2 fix2 (by decide +kernel) b2_76
    · exact via sym3 fix3 (by decide +kernel) b2_684
    · exact via sym3 fix3 (by decide +kernel) b2_683
    · exact via sym3 fix3 (by decide +kernel) b2_945
    · exact via sym3 fix3 (by decide +kernel) b2_717
    · exact via sym1 fix1 (by decide +kernel) b2_707
    · exact via sym1 fix1 (by decide +kernel) b2_706
    · exact b2_77
    · exact b2_76
    · exact via sym1 fix1 (by decide +kernel) b2_684
    · exact via sym1 fix1 (by decide +kernel) b2_683
    · exact via sym1 fix1 (by decide +kernel) b2_945
    · exact via sym1 fix1 (by decide +kernel) b2_717
    · exact b2_687
    · exact b2_609
    · exact via sym2 fix2 (by decide +kernel) b2_511
    · exact b2_712
    · exact via sym2 fix2 (by decide +kernel) b2_725
    · exact b2_725
    · exact b2_713
    · exact b2_708
    · exact via sym1 fix1 (by decide +kernel) b2_130
    · exact via sym2 fix2 (by decide +kernel) b2_561
    · exact b2_718
    · exact b2_709
    · exact via sym3 fix3 (by decide +kernel) b2_268
    · exact via sym2 fix2 (by decide +kernel) b2_531
    · exact via sym2 fix2 (by decide +kernel) b2_720
    · exact via sym1 fix1 (by decide +kernel) b2_709
    · exact via sym2 fix2 (by decide +kernel) b2_268
    · exact via sym3 fix3 (by decide +kernel) b2_531
    · exact via sym3 fix3 (by decide +kernel) b2_720
    · exact via sym1 fix1 (by decide +kernel) b2_708
    · exact b2_130
    · exact via sym3 fix3 (by decide +kernel) b2_561
    · exact via sym1 fix1 (by decide +kernel) b2_718
    · exact via sym2 fix2 (by decide +kernel) b2_687
    · exact b2_511
    · exact via sym2 fix2 (by decide +kernel) b2_609
    · exact via sym2 fix2 (by decide +kernel) b2_712
    · exact b2_710
    · exact via sym1 fix1 (by decide +kernel) b2_197
    · exact b2_649
    · exact b2_719
    · exact via sym2 fix2 (by decide +kernel) b2_710
    · exact via sym3 fix3 (by decide +kernel) b2_197
    · exact via sym2 fix2 (by decide +kernel) b2_649
    · exact via sym2 fix2 (by decide +kernel) b2_719
    · exact via sym3 fix3 (by decide +kernel) b2_710
    · exact via sym2 fix2 (by decide +kernel) b2_197
    · exact via sym3 fix3 (by decide +kernel) b2_649
    · exact via sym3 fix3 (by decide +kernel) b2_719
    · exact via sym1 fix1 (by decide +kernel) b2_710
    · exact b2_197
    · exact via sym1 fix1 (by decide +kernel) b2_649
    · exact via sym1 fix1 (by decide +kernel) b2_719
    · exact via sym2 fix2 (by decide +kernel) b2_709
    · exact via sym1 fix1 (by decide +kernel) b2_268
    · exact b2_531
    · exact b2_720
    · exact via sym2 fix2 (by decide +kernel) b2_708
    · exact via sym3 fix3 (by decide +kernel) b2_130
    · exact b2_561
    · exact via sym2 fix2 (by decide +kernel) b2_718
    · exact via sym3 fix3 (by decide +kernel) b2_708
    · exact via sym2 fix2 (by decide +kernel) b2_130
    · exact via sym1 fix1 (by decide +kernel) b2_561
    · exact via sym3 fix3 (by decide +kernel) b2_718
    · exact via sym3 fix3 (by decide +kernel) b2_709
    · exact b2_268
    · exact via sym1 fix1 (by decide +kernel) b2_531
    · exact via sym1 fix1 (by decide +kernel) b2_720
    · exact b2_714
    · exact via sym3 fix3 (by decide +kernel) b2_402
    · exact via sym1 fix1 (by decide +kernel) b2_402
    · exact b2_721
    · exact b2_715
    · exact via sym2 fix2 (by decide +kernel) b2_368
    · exact via sym1 fix1 (by decide +kernel) b2_368
    · exact b2_722
    · exact b2_716
    · exact b2_333
    · exact via sym1 fix1 (by decide +kernel) b2_333
    · exact via sym2 fix2 (by decide +kernel) b2_723
    · exact via sym2 fix2 (by decide +kernel) b2_716
    · exact via sym2 fix2 (by decide +kernel) b2_333
    · exact via sym3 fix3 (by decide +kernel) b2_333
    · exact b2_723
    · exact via sym1 fix1 (by decide +kernel) b2_715
    · exact b2_368
    · exact via sym3 fix3 (by decide +kernel) b2_368
    · exact via sym1 fix1 (by decide +kernel) b2_722
    · exact via sym1 fix1 (by decide +kernel) b2_714
    · exact b2_402
    · exact via sym2 fix2 (by decide +kernel) b2_402
    · exact via sym1 fix1 (by decide +kernel) b2_721
theorem b1_14 : Blocked tgt 9 s1_14 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_14 9 _ le
  decide +kernel
theorem b1_15 : Blocked tgt 9 s1_15 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_15 9 _ le
  decide +kernel
theorem b1_16 : Blocked tgt 9 s1_16 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_16 9 _ le
  decide +kernel
theorem b1_17 : Blocked tgt 9 s1_17 := by
  apply node_sound (nxt := [s2_703,s2_701,s2_688,s2_642,s2_619,a308,a309,s2_12,s2_5,a310,s2_712,s2_505,s2_478,a311,a312,s2_840,s2_728,a313,a314,s2_846,s2_755,a315,a316,s2_851,a317,a318,a319,a320,a321,s2_143,a322,a323,s2_640,a324,s2_512,a325,s2_841,s2_799,a326,s2_650,s2_847,a327,a328,a329,a330,s2_1036,s2_852,a331,a332,a333,a334,a335,a336,a337,s2_198,a338,a339,a340,a341,s2_528,s2_527,a342,a343,s2_874,s2_842,s2_837,s2_836,a344,a345,a346,a347,s2_987,s2_848,s2_839,s2_838,a348,a349,a350,a351,a352,s2_853,a353,a354,a355,a356,a357,a358,a359,a360,a361,a362,s2_223,s2_222,a363,a364,a365,a366,a367,a368,s2_532,s2_849,a369,a370,s2_562,s2_854,a371,a372,a373,a374,a375,s2_282,a376,a377,s2_843,a378,a379,s2_855,s2_844,a380,a381,s2_856,s2_845,s2_334,a382,s2_859,s2_850,a383,a384,s2_857,a385,s2_369,a386,a387,a388,s2_403,a389,a390])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_703
    · exact b2_701
    · exact b2_688
    · exact b2_642
    · exact b2_619
    · exact via sym2 fix2 (by decide +kernel) b2_525
    · exact via sym2 fix2 (by decide +kernel) b2_514
    · exact b2_12
    · exact b2_5
    · exact via sym2 fix2 (by decide +kernel) b2_523
    · exact b2_712
    · exact b2_505
    · exact b2_478
    · exact via sym2 fix2 (by decide +kernel) b2_485
    · exact via sym2 fix2 (by decide +kernel) b2_1033
    · exact b2_840
    · exact b2_728
    · exact via sym1 fix1 (by decide +kernel) b2_143
    · exact via sym2 fix2 (by decide +kernel) b2_564
    · exact b2_846
    · exact b2_755
    · exact via sym3 fix3 (by decide +kernel) b2_289
    · exact via sym2 fix2 (by decide +kernel) b2_534
    · exact b2_851
    · exact via sym1 fix1 (by decide +kernel) b2_755
    · exact via sym2 fix2 (by decide +kernel) b2_289
    · exact via sym3 fix3 (by decide +kernel) b2_534
    · exact via sym1 fix1 (by decide +kernel) b2_851
    · exact via sym1 fix1 (by decide +kernel) b2_728
    · exact b2_143
    · exact via sym3 fix3 (by decide +kernel) b2_564
    · exact via sym1 fix1 (by decide +kernel) b2_846
    · exact b2_640
    · exact via sym2 fix2 (by decide +kernel) b2_690
    · exact b2_512
    · exact via sym2 fix2 (by decide +kernel) b2_624
    · exact b2_841
    · exact b2_799
    · exact via sym1 fix1 (by decide +kernel) b2_198
    · exact b2_650
    · exact b2_847
    · exact via sym2 fix2 (by decide +kernel) b2_801
    · exact via sym3 fix3 (by decide +kernel) b2_219
    · exact via sym3 fix3 (by decide +kernel) b2_200
    · exact via sym2 fix2 (by decide +kernel) b2_652
    · exact b2_1036
    · exact b2_852
    · exact via sym3 fix3 (by decide +kernel) b2_801
    · exact via sym2 fix2 (by decide +kernel) b2_219
    · exact via sym2 fix2 (by decide +kernel) b2_200
    · exact via sym3 fix3 (by decide +kernel) b2_652
    · exact via sym1 fix1 (by decide +kernel) b2_1036
    · exact via sym1 fix1 (by decide +kernel) b2_852
    · exact via sym1 fix1 (by decide +kernel) b2_799
    · exact b2_198
    · exact via sym1 fix1 (by decide +kernel) b2_650
    · exact via sym1 fix1 (by decide +kernel) b2_847
    · exact via sym2 fix2 (by decide +kernel) b2_727
    · exact via sym2 fix2 (by decide +kernel) b2_726
    · exact b2_528
    · exact b2_527
    · exact via sym2 fix2 (by decide +kernel) b2_440
    · exact via sym2 fix2 (by decide +kernel) b2_439
    · exact b2_874
    · exact b2_842
    · exact b2_837
    · exact b2_836
    · exact via sym1 fix1 (by decide +kernel) b2_223
    · exact via sym1 fix1 (by decide +kernel) b2_222
    · exact via sym2 fix2 (by decide +kernel) b2_444
    · exact via sym2 fix2 (by decide +kernel) b2_443
    · exact b2_987
    · exact b2_848
    · exact b2_839
    · exact b2_838
    · exact via sym3 fix3 (by decide +kernel) b2_328
    · exact via sym3 fix3 (by decide +kernel) b2_327
    · exact via sym2 fix2 (by decide +kernel) b2_442
    · exact via sym2 fix2 (by decide +kernel) b2_441
    · exact via sym2 fix2 (by decide +kernel) b2_1004
    · exact b2_853
    · exact via sym1 fix1 (by decide +kernel) b2_839
    · exact via sym1 fix1 (by decide +kernel) b2_838
    · exact via sym2 fix2 (by decide +kernel) b2_328
    · exact via sym2 fix2 (by decide +kernel) b2_327
    · exact via sym3 fix3 (by decide +kernel) b2_442
    · exact via sym3 fix3 (by decide +kernel) b2_441
    · exact via sym3 fix3 (by decide +kernel) b2_1004
    · exact via sym1 fix1 (by decide +kernel) b2_853
    · exact via sym1 fix1 (by decide +kernel) b2_837
    · exact via sym1 fix1 (by decide +kernel) b2_836
    · exact b2_223
    · exact b2_222
    · exact via sym3 fix3 (by decide +kernel) b2_444
    · exact via sym3 fix3 (by decide +kernel) b2_443
    · exact via sym1 fix1 (by decide +kernel) b2_987
    · exact via sym1 fix1 (by decide +kernel) b2_848
    · exact via sym2 fix2 (by decide +kernel) b2_757
    · exact via sym1 fix1 (by decide +kernel) b2_282
    · exact b2_532
    · exact b2_849
    · exact via sym2 fix2 (by decide +kernel) b2_730
    · exact via sym3 fix3 (by decide +kernel) b2_151
    · exact b2_562
    · exact b2_854
    · exact via sym3 fix3 (by decide +kernel) b2_730
    · exact via sym2 fix2 (by decide +kernel) b2_151
    · exact via sym1 fix1 (by decide +kernel) b2_562
    · exact via sym1 fix1 (by decide +kernel) b2_854
    · exact via sym3 fix3 (by decide +kernel) b2_757
    · exact b2_282
    · exact via sym1 fix1 (by decide +kernel) b2_532
    · exact via sym1 fix1 (by decide +kernel) b2_849
    · exact b2_843
    · exact via sym3 fix3 (by decide +kernel) b2_405
    · exact via sym1 fix1 (by decide +kernel) b2_403
    · exact b2_855
    · exact b2_844
    · exact via sym2 fix2 (by decide +kernel) b2_371
    · exact via sym1 fix1 (by decide +kernel) b2_369
    · exact b2_856
    · exact b2_845
    · exact b2_334
    · exact via sym1 fix1 (by decide +kernel) b2_334
    · exact b2_859
    · exact b2_850
    · exact via sym2 fix2 (by decide +kernel) b2_336
    · exact via sym3 fix3 (by decide +kernel) b2_336
    · exact b2_857
    · exact via sym1 fix1 (by decide +kernel) b2_844
    · exact b2_369
    · exact via sym3 fix3 (by decide +kernel) b2_371
    · exact via sym1 fix1 (by decide +kernel) b2_856
    · exact via sym1 fix1 (by decide +kernel) b2_843
    · exact b2_403
    · exact via sym2 fix2 (by decide +kernel) b2_405
    · exact via sym1 fix1 (by decide +kernel) b2_855
theorem b1_18 : Blocked tgt 9 s1_18 := by
  apply node_sound (nxt := [s2_689,s2_644,s2_623,a391,a312,s2_840,a253,s2_725,s2_713,s2_504,s2_484,a392,a393,s2_12,s2_6,a225,s2_729,a394,a395,a396,a397,s2_866,s2_756,a398,a399,a400,a401,a402,a403,a404,a405,s2_184,s2_150,a406,a407,a408,a409,s2_513,a410,a411,s2_1033,a412,s2_798,s2_797,s2_796,s2_795,s2_446,s2_445,s2_648,s2_647,s2_646,s2_645,s2_874,s2_862,s2_800,a413,s2_651,s2_867,a414,a415,a416,a417,a418,a419,a420,a421,a422,s2_199,a423,a424,s2_501,a425,a426,s2_533,s2_868,a427,a428,a429,s2_563,s2_1034,a430,a431,a432,a433,a434,a435,a436,a437,s2_288,a438,a439,s2_861,s2_860,a440,a441,s2_448,s2_447,s2_1003,s2_869,a442,a443,a444,a445,a446,a447,a448,a449,a450,a451,a452,a453,a454,a455,a456,a457,a458,a459,s2_326,s2_325,a460,a461,a462,a463,s2_863,a464,a465,s2_870,s2_864,a466,a467,s2_871,s2_865,s2_335,a468,a469,a470,a471,a472,s2_872,a473,s2_370,a474,a475,a476,s2_404,a477,a478])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_689
    · exact b2_644
    · exact b2_623
    · exact via sym2 fix2 (by decide +kernel) b2_513
    · exact via sym2 fix2 (by decide +kernel) b2_1033
    · exact b2_840
    · exact via sym2 fix2 (by decide +kernel) b2_725
    · exact b2_725
    · exact b2_713
    · exact b2_504
    · exact b2_484
    · exact via sym2 fix2 (by decide +kernel) b2_504
    · exact via sym2 fix2 (by decide +kernel) b2_484
    · exact b2_12
    · exact b2_6
    · exact via sym2 fix2 (by decide +kernel) b2_501
    · exact b2_729
    · exact via sym1 fix1 (by decide +kernel) b2_184
    · exact via sym1 fix1 (by decide +kernel) b2_150
    · exact via sym2 fix2 (by decide +kernel) b2_563
    · exact via sym2 fix2 (by decide +kernel) b2_1034
    · exact b2_866
    · exact b2_756
    · exact via sym3 fix3 (by decide +kernel) b2_288
    · exact via sym2 fix2 (by decide +kernel) b2_533
    · exact via sym2 fix2 (by decide +kernel) b2_868
    · exact via sym1 fix1 (by decide +kernel) b2_756
    · exact via sym2 fix2 (by decide +kernel) b2_288
    · exact via sym3 fix3 (by decide +kernel) b2_533
    · exact via sym3 fix3 (by decide +kernel) b2_868
    · exact via sym1 fix1 (by decide +kernel) b2_729
    · exact b2_184
    · exact b2_150
    · exact via sym3 fix3 (by decide +kernel) b2_563
    · exact via sym3 fix3 (by decide +kernel) b2_1034
    · exact via sym1 fix1 (by decide +kernel) b2_866
    · exact via sym2 fix2 (by decide +kernel) b2_689
    · exact b2_513
    · exact via sym2 fix2 (by decide +kernel) b2_644
    · exact via sym2 fix2 (by decide +kernel) b2_623
    · exact b2_1033
    · exact via sym2 fix2 (by decide +kernel) b2_840
    · exact b2_798
    · exact b2_797
    · exact b2_796
    · exact b2_795
    · exact b2_446
    · exact b2_445
    · exact b2_648
    · exact b2_647
    · exact b2_646
    · exact b2_645
    · exact b2_874
    · exact b2_862
    · exact b2_800
    · exact via sym1 fix1 (by decide +kernel) b2_199
    · exact b2_651
    · exact b2_867
    · exact via sym2 fix2 (by decide +kernel) b2_800
    · exact via sym3 fix3 (by decide +kernel) b2_199
    · exact via sym2 fix2 (by decide +kernel) b2_651
    · exact via sym2 fix2 (by decide +kernel) b2_867
    · exact via sym3 fix3 (by decide +kernel) b2_800
    · exact via sym2 fix2 (by decide +kernel) b2_199
    · exact via sym3 fix3 (by decide +kernel) b2_651
    · exact via sym3 fix3 (by decide +kernel) b2_867
    · exact via sym1 fix1 (by decide +kernel) b2_800
    · exact b2_199
    · exact via sym1 fix1 (by decide +kernel) b2_651
    · exact via sym1 fix1 (by decide +kernel) b2_867
    · exact b2_501
    · exact via sym2 fix2 (by decide +kernel) b2_756
    · exact via sym1 fix1 (by decide +kernel) b2_288
    · exact b2_533
    · exact b2_868
    · exact via sym2 fix2 (by decide +kernel) b2_729
    · exact via sym3 fix3 (by decide +kernel) b2_184
    · exact via sym3 fix3 (by decide +kernel) b2_150
    · exact b2_563
    · exact b2_1034
    · exact via sym2 fix2 (by decide +kernel) b2_866
    · exact via sym3 fix3 (by decide +kernel) b2_729
    · exact via sym2 fix2 (by decide +kernel) b2_184
    · exact via sym2 fix2 (by decide +kernel) b2_150
    · exact via sym1 fix1 (by decide +kernel) b2_563
    · exact via sym1 fix1 (by decide +kernel) b2_1034
    · exact via sym3 fix3 (by decide +kernel) b2_866
    · exact via sym3 fix3 (by decide +kernel) b2_756
    · exact b2_288
    · exact via sym1 fix1 (by decide +kernel) b2_533
    · exact via sym1 fix1 (by decide +kernel) b2_868
    · exact b2_861
    · exact b2_860
    · exact via sym1 fix1 (by decide +kernel) b2_326
    · exact via sym1 fix1 (by decide +kernel) b2_325
    · exact b2_448
    · exact b2_447
    · exact b2_1003
    · exact b2_869
    · exact via sym2 fix2 (by decide +kernel) b2_861
    · exact via sym2 fix2 (by decide +kernel) b2_860
    · exact via sym3 fix3 (by decide +kernel) b2_326
    · exact via sym3 fix3 (by decide +kernel) b2_325
    · exact via sym2 fix2 (by decide +kernel) b2_448
    · exact via sym2 fix2 (by decide +kernel) b2_447
    · exact via sym2 fix2 (by decide +kernel) b2_1003
    · exact via sym2 fix2 (by decide +kernel) b2_869
    · exact via sym3 fix3 (by decide +kernel) b2_861
    · exact via sym3 fix3 (by decide +kernel) b2_860
    · exact via sym2 fix2 (by decide +kernel) b2_326
    · exact via sym2 fix2 (by decide +kernel) b2_325
    · exact via sym3 fix3 (by decide +kernel) b2_448
    · exact via sym3 fix3 (by decide +kernel) b2_447
    · exact via sym3 fix3 (by decide +kernel) b2_1003
    · exact via sym3 fix3 (by decide +kernel) b2_869
    · exact via sym1 fix1 (by decide +kernel) b2_861
    · exact via sym1 fix1 (by decide +kernel) b2_860
    · exact b2_326
    · exact b2_325
    · exact via sym1 fix1 (by decide +kernel) b2_448
    · exact via sym1 fix1 (by decide +kernel) b2_447
    · exact via sym1 fix1 (by decide +kernel) b2_1003
    · exact via sym1 fix1 (by decide +kernel) b2_869
    · exact b2_863
    · exact via sym3 fix3 (by decide +kernel) b2_404
    · exact via sym1 fix1 (by decide +kernel) b2_404
    · exact b2_870
    · exact b2_864
    · exact via sym2 fix2 (by decide +kernel) b2_370
    · exact via sym1 fix1 (by decide +kernel) b2_370
    · exact b2_871
    · exact b2_865
    · exact b2_335
    · exact via sym1 fix1 (by decide +kernel) b2_335
    · exact via sym2 fix2 (by decide +kernel) b2_872
    · exact via sym2 fix2 (by decide +kernel) b2_865
    · exact via sym2 fix2 (by decide +kernel) b2_335
    · exact via sym3 fix3 (by decide +kernel) b2_335
    · exact b2_872
    · exact via sym1 fix1 (by decide +kernel) b2_864
    · exact b2_370
    · exact via sym3 fix3 (by decide +kernel) b2_370
    · exact via sym1 fix1 (by decide +kernel) b2_871
    · exact via sym1 fix1 (by decide +kernel) b2_863
    · exact b2_404
    · exact via sym2 fix2 (by decide +kernel) b2_404
    · exact via sym1 fix1 (by decide +kernel) b2_870
theorem b1_19 : Blocked tgt 9 s1_19 := by
  intro m le c
  apply rejects_sound cycle1 i5 6 tgt small1 hot1 [] s1_19 9 _ le
  decide +kernel
theorem b1_20 : Blocked tgt 9 s1_20 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_20 9 _ le
  decide +kernel
theorem b1_21 : Blocked tgt 9 s1_21 := by
  intro m le c
  apply rejects_sound cycle0 i5 6 tgt small0 hot0 [] s1_21 9 _ le
  decide +kernel
theorem b1_22 : Blocked tgt 9 s1_22 := by
  apply node_sound (nxt := [s2_691,s2_629,a479,s2_846,s2_718,s2_506,s2_490,a480,a397,s2_866,s2_749,s2_748,s2_731,a481,a482,a483,a484,s2_12,s2_7,a485,s2_758,a486,a487,a488,a489,s2_950,a490,a491,a492,s2_955,a493,s2_157,a494,s2_962,a495,s2_515,a496,a497,s2_802,a498,s2_670,s2_653,a499,s2_946,s2_823,s2_822,a500,a501,s2_674,s2_673,s2_987,s2_947,a502,a503,a504,s2_951,a505,a506,a507,s2_956,a508,s2_201,a509,s2_963,a510,a511,a512,a513,s2_535,s2_948,a514,a515,a516,a517,s2_556,s2_555,s2_1003,s2_949,a518,a519,s2_565,s2_952,a520,a521,a522,s2_957,a523,s2_295,a524,s2_964,a525,s2_875,a526,a527,a528,a529,s2_953,s2_895,a530,a531,a532,a533,s2_958,s2_915,s2_355,s2_337,a534,a535,s2_965,a536,a537,a538,a539,a540,a541,a542,a543,a544,a545,s2_1007,s2_954,a546,a547,a548,a549,a550,a551,s2_1014,s2_959,a552,a553,s2_359,s2_358,a554,a555,a556,s2_966,a557,a558,a559,s2_960,a560,s2_372,a561,s2_967,a562,s2_406,a563,s2_968])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_691
    · exact b2_629
    · exact via sym2 fix2 (by decide +kernel) b2_520
    · exact b2_846
    · exact b2_718
    · exact b2_506
    · exact b2_490
    · exact via sym2 fix2 (by decide +kernel) b2_497
    · exact via sym2 fix2 (by decide +kernel) b2_1034
    · exact b2_866
    · exact b2_749
    · exact b2_748
    · exact b2_731
    · exact via sym1 fix1 (by decide +kernel) b2_183
    · exact via sym1 fix1 (by decide +kernel) b2_177
    · exact via sym2 fix2 (by decide +kernel) b2_585
    · exact via sym2 fix2 (by decide +kernel) b2_570
    · exact b2_12
    · exact b2_7
    · exact via sym2 fix2 (by decide +kernel) b2_576
    · exact b2_758
    · exact via sym3 fix3 (by decide +kernel) b2_324
    · exact via sym3 fix3 (by decide +kernel) b2_312
    · exact via sym2 fix2 (by decide +kernel) b2_540
    · exact via sym2 fix2 (by decide +kernel) b2_1035
    · exact b2_950
    · exact via sym1 fix1 (by decide +kernel) b2_770
    · exact via sym2 fix2 (by decide +kernel) b2_304
    · exact via sym3 fix3 (by decide +kernel) b2_543
    · exact b2_955
    · exact via sym1 fix1 (by decide +kernel) b2_743
    · exact b2_157
    · exact via sym3 fix3 (by decide +kernel) b2_573
    · exact b2_962
    · exact via sym2 fix2 (by decide +kernel) b2_696
    · exact b2_515
    · exact via sym2 fix2 (by decide +kernel) b2_636
    · exact via sym2 fix2 (by decide +kernel) b2_854
    · exact b2_802
    · exact via sym1 fix1 (by decide +kernel) b2_213
    · exact b2_670
    · exact b2_653
    · exact via sym1 fix1 (by decide +kernel) b2_1026
    · exact b2_946
    · exact b2_823
    · exact b2_822
    · exact via sym1 fix1 (by decide +kernel) b2_60
    · exact via sym1 fix1 (by decide +kernel) b2_61
    · exact b2_674
    · exact b2_673
    · exact b2_987
    · exact b2_947
    · exact via sym2 fix2 (by decide +kernel) b2_807
    · exact via sym3 fix3 (by decide +kernel) b2_209
    · exact via sym2 fix2 (by decide +kernel) b2_658
    · exact b2_951
    · exact via sym3 fix3 (by decide +kernel) b2_810
    · exact via sym2 fix2 (by decide +kernel) b2_206
    · exact via sym3 fix3 (by decide +kernel) b2_661
    · exact b2_956
    · exact via sym1 fix1 (by decide +kernel) b2_813
    · exact b2_201
    · exact via sym1 fix1 (by decide +kernel) b2_665
    · exact b2_963
    · exact via sym2 fix2 (by decide +kernel) b2_776
    · exact via sym2 fix2 (by decide +kernel) b2_763
    · exact via sym1 fix1 (by decide +kernel) b2_322
    · exact via sym1 fix1 (by decide +kernel) b2_316
    · exact b2_535
    · exact b2_948
    · exact via sym2 fix2 (by decide +kernel) b2_782
    · exact via sym2 fix2 (by decide +kernel) b2_781
    · exact via sym1 fix1 (by decide +kernel) b2_64
    · exact via sym1 fix1 (by decide +kernel) b2_65
    · exact b2_556
    · exact b2_555
    · exact b2_1003
    · exact b2_949
    · exact via sym2 fix2 (by decide +kernel) b2_736
    · exact via sym3 fix3 (by decide +kernel) b2_173
    · exact b2_565
    · exact b2_952
    · exact via sym3 fix3 (by decide +kernel) b2_739
    · exact via sym2 fix2 (by decide +kernel) b2_166
    · exact via sym1 fix1 (by decide +kernel) b2_577
    · exact b2_957
    · exact via sym3 fix3 (by decide +kernel) b2_766
    · exact b2_295
    · exact via sym1 fix1 (by decide +kernel) b2_547
    · exact b2_964
    · exact via sym1 fix1 (by decide +kernel) b2_176
    · exact b2_875
    · exact via sym3 fix3 (by decide +kernel) b2_424
    · exact via sym3 fix3 (by decide +kernel) b2_414
    · exact via sym1 fix1 (by decide +kernel) b2_417
    · exact via sym1 fix1 (by decide +kernel) b2_1029
    · exact b2_953
    · exact b2_895
    · exact via sym2 fix2 (by decide +kernel) b2_390
    · exact via sym2 fix2 (by decide +kernel) b2_377
    · exact via sym1 fix1 (by decide +kernel) b2_384
    · exact via sym1 fix1 (by decide +kernel) b2_1028
    · exact b2_958
    · exact b2_915
    · exact b2_355
    · exact b2_337
    · exact via sym1 fix1 (by decide +kernel) b2_349
    · exact via sym1 fix1 (by decide +kernel) b2_1027
    · exact b2_965
    · exact via sym2 fix2 (by decide +kernel) b2_894
    · exact via sym2 fix2 (by decide +kernel) b2_892
    · exact via sym2 fix2 (by decide +kernel) b2_893
    · exact via sym2 fix2 (by decide +kernel) b2_891
    · exact via sym3 fix3 (by decide +kernel) b2_429
    · exact via sym3 fix3 (by decide +kernel) b2_432
    · exact via sym3 fix3 (by decide +kernel) b2_430
    · exact via sym3 fix3 (by decide +kernel) b2_431
    · exact via sym1 fix1 (by decide +kernel) b2_70
    · exact via sym1 fix1 (by decide +kernel) b2_71
    · exact b2_1007
    · exact b2_954
    · exact via sym3 fix3 (by decide +kernel) b2_912
    · exact via sym3 fix3 (by decide +kernel) b2_911
    · exact via sym2 fix2 (by decide +kernel) b2_397
    · exact via sym2 fix2 (by decide +kernel) b2_396
    · exact via sym1 fix1 (by decide +kernel) b2_68
    · exact via sym1 fix1 (by decide +kernel) b2_69
    · exact b2_1014
    · exact b2_959
    · exact via sym1 fix1 (by decide +kernel) b2_927
    · exact via sym1 fix1 (by decide +kernel) b2_928
    · exact b2_359
    · exact b2_358
    · exact via sym1 fix1 (by decide +kernel) b2_66
    · exact via sym1 fix1 (by decide +kernel) b2_67
    · exact via sym2 fix2 (by decide +kernel) b2_1023
    · exact b2_966
    · exact via sym2 fix2 (by decide +kernel) b2_920
    · exact via sym2 fix2 (by decide +kernel) b2_342
    · exact via sym3 fix3 (by decide +kernel) b2_345
    · exact b2_960
    · exact via sym2 fix2 (by decide +kernel) b2_900
    · exact b2_372
    · exact via sym3 fix3 (by decide +kernel) b2_380
    · exact b2_967
    · exact via sym3 fix3 (by decide +kernel) b2_880
    · exact b2_406
    · exact via sym2 fix2 (by decide +kernel) b2_411
    · exact b2_968
theorem b1_23 : Blocked tgt 9 s1_23 := by
  apply node_sound (nxt := [s2_702,s2_692,s2_643,s2_630,a564,s2_847,s2_719,s2_491,a565,s2_867,s2_732,a566,a567,a568,a499,s2_946,s2_752,s2_751,a156,a569,a570,a571,s2_987,s2_969,s2_759,a572,a573,s2_972,a574,a575,a576,s2_976,a577,s2_158,a578,a579,a580,s2_526,s2_516,a581,a582,a583,s2_819,s2_818,s2_803,a584,a585,s2_672,s2_654,s2_12,s2_8,s2_664,a586,a587,a588,a589,s2_1037,s2_973,a590,a591,a592,a593,s2_1038,s2_977,a594,s2_202,a595,s2_981,a596,a597,s2_552,s2_536,a598,s2_970,a599,a600,a601,a602,s2_558,s2_557,s2_1004,s2_971,a603,a604,s2_566,a605,a606,a607,a608,a609,a610,s2_296,a611,s2_982,a612,a613,s2_876,a614,a615,a616,s2_974,s2_896,a617,a618,s2_978,s2_916,s2_338,a619,s2_983,a620,a621,a622,a623,a624,a625,s2_1008,s2_975,a626,a627,a628,a629,a630,a631,s2_1015,s2_979,a632,a633,s2_361,s2_360,a634,a635,a636,s2_984,a637,a638,a639,s2_980,a640,s2_373,a641,s2_985,a642,s2_407,a643,s2_986])
  · decide +kernel
  · intro R mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b2_702
    · exact b2_692
    · exact b2_643
    · exact b2_630
    · exact via sym2 fix2 (by decide +kernel) b2_519
    · exact b2_847
    · exact b2_719
    · exact b2_491
    · exact via sym2 fix2 (by decide +kernel) b2_496
    · exact b2_867
    · exact b2_732
    · exact via sym1 fix1 (by decide +kernel) b2_178
    · exact via sym2 fix2 (by decide +kernel) b2_582
    · exact via sym2 fix2 (by decide +kernel) b2_569
    · exact via sym1 fix1 (by decide +kernel) b2_1026
    · exact b2_946
    · exact b2_752
    · exact b2_751
    · exact via sym1 fix1 (by decide +kernel) b2_48
    · exact via sym1 fix1 (by decide +kernel) b2_49
    · exact via sym2 fix2 (by decide +kernel) b2_589
    · exact via sym2 fix2 (by decide +kernel) b2_588
    · exact b2_987
    · exact b2_969
    · exact b2_759
    · exact via sym3 fix3 (by decide +kernel) b2_311
    · exact via sym2 fix2 (by decide +kernel) b2_539
    · exact b2_972
    · exact via sym1 fix1 (by decide +kernel) b2_771
    · exact via sym2 fix2 (by decide +kernel) b2_303
    · exact via sym3 fix3 (by decide +kernel) b2_542
    · exact b2_976
    · exact via sym1 fix1 (by decide +kernel) b2_744
    · exact b2_158
    · exact via sym3 fix3 (by decide +kernel) b2_572
    · exact via sym1 fix1 (by decide +kernel) b2_963
    · exact via sym2 fix2 (by decide +kernel) b2_695
    · exact b2_526
    · exact b2_516
    · exact via sym2 fix2 (by decide +kernel) b2_635
    · exact via sym2 fix2 (by decide +kernel) b2_1036
    · exact via sym2 fix2 (by decide +kernel) b2_852
    · exact b2_819
    · exact b2_818
    · exact b2_803
    · exact via sym1 fix1 (by decide +kernel) b2_218
    · exact via sym1 fix1 (by decide +kernel) b2_214
    · exact b2_672
    · exact b2_654
    · exact b2_12
    · exact b2_8
    · exact b2_664
    · exact via sym2 fix2 (by decide +kernel) b2_806
    · exact via sym3 fix3 (by decide +kernel) b2_221
    · exact via sym3 fix3 (by decide +kernel) b2_208
    · exact via sym2 fix2 (by decide +kernel) b2_657
    · exact b2_1037
    · exact b2_973
    · exact via sym3 fix3 (by decide +kernel) b2_809
    · exact via sym2 fix2 (by decide +kernel) b2_220
    · exact via sym2 fix2 (by decide +kernel) b2_205
    · exact via sym3 fix3 (by decide +kernel) b2_660
    · exact b2_1038
    · exact b2_977
    · exact via sym1 fix1 (by decide +kernel) b2_814
    · exact b2_202
    · exact via sym1 fix1 (by decide +kernel) b2_666
    · exact b2_981
    · exact via sym2 fix2 (by decide +kernel) b2_762
    · exact via sym1 fix1 (by decide +kernel) b2_317
    · exact b2_552
    · exact b2_536
    · exact via sym1 fix1 (by decide +kernel) b2_1030
    · exact b2_970
    · exact via sym2 fix2 (by decide +kernel) b2_780
    · exact via sym2 fix2 (by decide +kernel) b2_779
    · exact via sym1 fix1 (by decide +kernel) b2_52
    · exact via sym1 fix1 (by decide +kernel) b2_53
    · exact b2_558
    · exact b2_557
    · exact b2_1004
    · exact b2_971
    · exact via sym2 fix2 (by decide +kernel) b2_735
    · exact via sym3 fix3 (by decide +kernel) b2_172
    · exact b2_566
    · exact via sym2 fix2 (by decide +kernel) b2_951
    · exact via sym3 fix3 (by decide +kernel) b2_738
    · exact via sym2 fix2 (by decide +kernel) b2_165
    · exact via sym1 fix1 (by decide +kernel) b2_578
    · exact via sym3 fix3 (by decide +kernel) b2_956
    · exact via sym3 fix3 (by decide +kernel) b2_765
    · exact b2_296
    · exact via sym1 fix1 (by decide +kernel) b2_548
    · exact b2_982
    · exact via sym1 fix1 (by decide +kernel) b2_212
    · exact via sym2 fix2 (by decide +kernel) b2_883
    · exact b2_876
    · exact via sym3 fix3 (by decide +kernel) b2_413
    · exact via sym1 fix1 (by decide +kernel) b2_422
    · exact via sym1 fix1 (by decide +kernel) b2_418
    · exact b2_974
    · exact b2_896
    · exact via sym2 fix2 (by decide +kernel) b2_376
    · exact via sym1 fix1 (by decide +kernel) b2_385
    · exact b2_978
    · exact b2_916
    · exact b2_338
    · exact via sym1 fix1 (by decide +kernel) b2_350
    · exact b2_983
    · exact via sym2 fix2 (by decide +kernel) b2_890
    · exact via sym2 fix2 (by decide +kernel) b2_889
    · exact via sym3 fix3 (by decide +kernel) b2_428
    · exact via sym3 fix3 (by decide +kernel) b2_427
    · exact via sym1 fix1 (by decide +kernel) b2_58
    · exact via sym1 fix1 (by decide +kernel) b2_59
    · exact b2_1008
    · exact b2_975
    · exact via sym3 fix3 (by decide +kernel) b2_910
    · exact via sym3 fix3 (by decide +kernel) b2_909
    · exact via sym2 fix2 (by decide +kernel) b2_395
    · exact via sym2 fix2 (by decide +kernel) b2_394
    · exact via sym1 fix1 (by decide +kernel) b2_56
    · exact via sym1 fix1 (by decide +kernel) b2_57
    · exact b2_1015
    · exact b2_979
    · exact via sym1 fix1 (by decide +kernel) b2_929
    · exact via sym1 fix1 (by decide +kernel) b2_930
    · exact b2_361
    · exact b2_360
    · exact via sym1 fix1 (by decide +kernel) b2_54
    · exact via sym1 fix1 (by decide +kernel) b2_55
    · exact via sym2 fix2 (by decide +kernel) b2_1022
    · exact b2_984
    · exact via sym2 fix2 (by decide +kernel) b2_919
    · exact via sym2 fix2 (by decide +kernel) b2_341
    · exact via sym3 fix3 (by decide +kernel) b2_344
    · exact b2_980
    · exact via sym2 fix2 (by decide +kernel) b2_899
    · exact b2_373
    · exact via sym3 fix3 (by decide +kernel) b2_379
    · exact b2_985
    · exact via sym3 fix3 (by decide +kernel) b2_879
    · exact b2_407
    · exact via sym2 fix2 (by decide +kernel) b2_410
    · exact b2_986
end ThetaCert
