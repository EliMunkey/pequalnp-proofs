import PetersenLocalChildren
import Q1020K12L1S0Local
import Q1020K12L2S0
import Q1020K12L2S1
import Q1020K12L2S2
import Q1020K12L2S4
import Q1020K12L2S5
import Q1020K12L2S6
import Q1020K12L2S9
import Q1020K12L2S10
import Q1020K12L2S11
import Q1020K12L2S12
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L1S0Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
private theorem pair1_3_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_37,s2_36,a121,a122,a123,s2_244,s2_430,s2_245]) (hints := [778,0,778,1,8488,6,8488,7,778,2,778,3,8488,4,8488,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_37,s2_36,a121,a122,a123,s2_244,s2_430,s2_245], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_37) (b2_37 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_36) (b2_36 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a121) (via sym5 fix5 (by decide +kernel) (b2_31 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a122) (via sym5 fix5 (by decide +kernel) (b2_30 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a123) (via sym1 fix1 (by decide +kernel) (b2_422 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_244) (b2_244 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_430) (b2_430 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_245) (b2_245 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_71,s2_69,a124,a125,a126,s2_251,s2_488,s2_252]) (hints := [777,0,777,1,9772,6,9772,7,777,2,777,3,9772,4,9772,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_71,s2_69,a124,a125,a126,s2_251,s2_488,s2_252], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_71) (b2_71 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_69) (b2_69 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a124) (via sym4 fix4 (by decide +kernel) (b2_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a125) (via sym4 fix4 (by decide +kernel) (b2_10 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a126) (via sym2 fix2 (by decide +kernel) (b2_464 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_251) (b2_251 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_488) (b2_488 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_252) (b2_252 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_202,s2_201,a127,a128,a129,s2_257,a130,s2_258]) (hints := [1546,0,1546,1,9770,6,9770,7,1546,2,1546,3,9770,4,9770,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_202,s2_201,a127,a128,a129,s2_257,a130,s2_258], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_202) (b2_202 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_201) (b2_201 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a127) (via sym5 fix5 (by decide +kernel) (b2_25 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a128) (via sym5 fix5 (by decide +kernel) (b2_24 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a129) (via sym3 fix3 (by decide +kernel) (b2_386 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_257) (b2_257 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a130) (via sym2 fix2 (by decide +kernel) (b2_434 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_258) (b2_258 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a131,a132,s2_31,s2_30,a133,a134,a135,a136]) (hints := [18504,0,18504,1,10280,6,10280,7,18504,2,18504,3,10280,4,10280,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a131,a132,s2_31,s2_30,a133,a134,a135,a136], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a131) (via sym5 fix5 (by decide +kernel) (b2_37 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a132) (via sym5 fix5 (by decide +kernel) (b2_36 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_31) (b2_31 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_30) (b2_30 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a133) (via sym4 fix4 (by decide +kernel) (b2_422 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a134) (via sym5 fix5 (by decide +kernel) (b2_244 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a135) (via sym5 fix5 (by decide +kernel) (b2_430 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a136) (via sym5 fix5 (by decide +kernel) (b2_245 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a137,a138,s2_25,s2_24,a139,a140,a141,a142]) (hints := [20552,0,20552,1,28776,6,28776,7,20552,2,20552,3,28776,4,28776,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a137,a138,s2_25,s2_24,a139,a140,a141,a142], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a137) (via sym5 fix5 (by decide +kernel) (b2_202 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a138) (via sym5 fix5 (by decide +kernel) (b2_201 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_25) (b2_25 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_24) (b2_24 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a139) (via sym7 fix7 (by decide +kernel) (b2_386 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a140) (via sym5 fix5 (by decide +kernel) (b2_257 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a141) (via sym6 fix6 (by decide +kernel) (b2_434 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a142) (via sym5 fix5 (by decide +kernel) (b2_258 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_1,a143,s2_267,s2_266]) (hints := [8454,0,41093,1,8454,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_1,a143,s2_267,s2_266], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_1) (b2_1 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a143) (via sym1 fix1 (by decide +kernel) (b2_478 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_267) (b2_267 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_266) (b2_266 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a144,a145,a146,a147,a148,a149,a150,a151]) (hints := [16906,0,16906,1,25130,6,25130,7,16906,2,16906,3,25130,4,25130,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a144,a145,a146,a147,a148,a149,a150,a151], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a144) (via sym5 fix5 (by decide +kernel) (b2_71 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a145) (via sym5 fix5 (by decide +kernel) (b2_69 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a146) (via sym1 fix1 (by decide +kernel) (b2_11 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a147) (via sym1 fix1 (by decide +kernel) (b2_10 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a148) (via sym6 fix6 (by decide +kernel) (b2_464 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a149) (via sym5 fix5 (by decide +kernel) (b2_251 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a150) (via sym5 fix5 (by decide +kernel) (b2_488 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a151) (via sym5 fix5 (by decide +kernel) (b2_252 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_6,s2_1,a152,s2_277,s2_276]) (hints := [33801,0,33801,1,40997,2,3,4]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_6,s2_1,a152,s2_277,s2_276], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_6) (b2_6 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_1) (b2_1 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a152) (via sym1 fix1 (by decide +kernel) (b2_529 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_277) (b2_277 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_276) (b2_276 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_237,a153,a154,s2_253]) (hints := [1544,8484,1544,0,773,774,773,3,772,774,1544,1,772,8484,773,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_237,a153,a154,s2_253], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_237) (b2_237 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a153) (via sym4 fix4 (by decide +kernel) (b2_204 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a154) (via sym5 fix5 (by decide +kernel) (b2_235 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_253) (b2_253 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_238,a155,a156,s2_259]) (hints := [774,774,1542,0,8488,9512,34181,3,1542,9512,1542,1,774,774,34181,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_238,a155,a156,s2_259], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_238) (b2_238 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a155) (via sym5 fix5 (by decide +kernel) (b2_225 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a156) (via sym5 fix5 (by decide +kernel) (b2_233 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_259) (b2_259 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_239,s2_230,a157,s2_261]) (hints := [774,774,10276,0,782,2830,18757,3,2822,2830,10276,1,774,774,18757,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_239,s2_230,a157,s2_261], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_239) (b2_239 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_230) (b2_230 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a157) (via sym5 fix5 (by decide +kernel) (b2_230 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_261) (b2_261 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_240,s2_222,a158,a159]) (hints := [774,774,20548,0,790,4886,20805,3,4870,4886,20548,1,774,774,20805,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_240,s2_222,a158,a159], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_240) (b2_240 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_222) (b2_222 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a158) (via sym5 fix5 (by decide +kernel) (b2_232 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a159) (via sym5 fix5 (by decide +kernel) (b2_263 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_241,a160,a161,s2_268]) (hints := [774,774,41092,0,8484,8484,41349,3,8484,8484,41092,1,774,774,41349,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_241,a160,a161,s2_268], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_241) (b2_241 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a160) (via sym2 fix2 (by decide +kernel) (b2_205 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a161) (via sym5 fix5 (by decide +kernel) (b2_234 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_268) (b2_268 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_242,a162,a163,a164]) (hints := [774,774,16902,0,18445,24932,18701,3,16902,24932,16902,1,774,774,18701,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_242,a162,a163,a164], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_242) (b2_242 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a162) (via sym1 fix1 (by decide +kernel) (b2_43 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a163) (via sym5 fix5 (by decide +kernel) (b2_231 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a164) (via sym5 fix5 (by decide +kernel) (b2_262 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_243,s2_41,a165,s2_273]) (hints := [774,774,33800,0,33801,33670,34057,3,33542,33670,33800,1,774,774,34057,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_243,s2_41,a165,s2_273], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_243) (b2_243 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_41) (b2_41 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a165) (via sym5 fix5 (by decide +kernel) (b2_236 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_273) (b2_273 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_246,a166,a167,s2_260]) (hints := [773,773,33924,0,1542,1544,1542,3,1540,1544,33924,1,1540,773,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_246,a166,a167,s2_260], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_246) (b2_246 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a166) (via sym5 fix5 (by decide +kernel) (b2_228 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a167) (via sym7 fix7 (by decide +kernel) (b2_206 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_260) (b2_260 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a168,s2_231,a169,s2_262]) (hints := [773,773,10276,0,781,2829,10790,3,2821,2829,10276,1,773,773,10790,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a168,s2_231,a169,s2_262], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a168) (via sym5 fix5 (by decide +kernel) (b2_242 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_231) (b2_231 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a169) (via sym4 fix4 (by decide +kernel) (b2_43 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_262) (b2_262 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_247,s2_223,a170,s2_264]) (hints := [773,773,20548,0,789,4885,37510,3,4869,4885,20548,1,773,773,37510,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_247,s2_223,a170,s2_264], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_247) (b2_247 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_223) (b2_223 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a170) (via sym7 fix7 (by decide +kernel) (b2_50 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_264) (b2_264 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_248,a171,a172,s2_269]) (hints := [773,773,41092,0,9768,9768,41606,3,9768,9768,41092,1,773,773,41606,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_248,a171,a172,s2_269], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_248) (b2_248 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a171) (via sym2 fix2 (by decide +kernel) (b2_89 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a172) (via sym4 fix4 (by decide +kernel) (b2_79 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_269) (b2_269 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_249,s2_219,a173,s2_271]) (hints := [773,773,18444,0,16902,16964,16902,3,16900,16964,18444,1,16900,773,16902,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_249,s2_219,a173,s2_271], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_249) (b2_249 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_219) (b2_219 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a173) (via sym4 fix4 (by decide +kernel) (b2_219 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_271) (b2_271 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_250,s2_77,a174,s2_274]) (hints := [773,773,33800,0,36886,33669,37398,3,33541,33669,33800,1,773,773,37398,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_250,s2_77,a174,s2_274], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_250) (b2_250 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_77) (b2_77 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a174) (via sym7 fix7 (by decide +kernel) (b2_115 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_274) (b2_274 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a175,s2_232,a176,s2_263]) (hints := [1542,1542,10276,0,1550,3598,11304,3,3590,3598,10276,1,1542,1542,11304,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a175,s2_232,a176,s2_263], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a175) (via sym5 fix5 (by decide +kernel) (b2_240 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_232) (b2_232 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a176) (via sym5 fix5 (by decide +kernel) (b2_222 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_263) (b2_263 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_254,s2_224,a177,s2_265]) (hints := [1542,1542,20548,0,1558,5654,21576,3,5638,5654,20548,1,1542,1542,21576,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_254,s2_224,a177,s2_265], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_254) (b2_254 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_224) (b2_224 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a177) (via sym5 fix5 (by decide +kernel) (b2_224 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_265) (b2_265 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_255,a178,a179,a180,s2_278,s2_270]) (hints := [1544,1544,41094,0,9768,9768,4,5,9768,9768,41094,1,1544,1544,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_255,a178,a179,a180,s2_278,s2_270], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_255) (b2_255 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a178) (via sym2 fix2 (by decide +kernel) (b2_48 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a179) (via sym5 fix5 (by decide +kernel) (b2_227 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a180) (via sym5 fix5 (by decide +kernel) (b2_226 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_278) (b2_278 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_270) (b2_270 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a181,a182,a183,a184]) (hints := [1542,1542,16902,0,18448,50372,19472,3,16902,50372,16902,1,1542,1542,19472,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a181,a182,a183,a184], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a181) (via sym5 fix5 (by decide +kernel) (b2_247 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a182) (via sym3 fix3 (by decide +kernel) (b2_50 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a183) (via sym5 fix5 (by decide +kernel) (b2_223 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a184) (via sym5 fix5 (by decide +kernel) (b2_264 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_256,s2_203,a185,s2_275]) (hints := [1542,1542,36884,0,33800,33924,33800,3,33796,33924,36884,1,33796,1542,33800,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_256,s2_203,a185,s2_275], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_256) (b2_256 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_203) (b2_203 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a185) (via sym5 fix5 (by decide +kernel) (b2_229 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_275) (b2_275 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a186,s2_225,s2_233,a187]) (hints := [10276,10276,20548,0,10292,14388,39052,3,14372,14388,20548,1,10276,10276,39052,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a186,s2_225,s2_233,a187], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a186) (via sym5 fix5 (by decide +kernel) (b2_238 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_225) (b2_225 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_233) (b2_233 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a187) (via sym5 fix5 (by decide +kernel) (b2_259 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a188,a189,s2_234,a190]) (hints := [18500,18500,41092,0,10276,10276,43148,3,10276,10276,41092,1,18500,18500,43148,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a188,a189,s2_234,a190], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a188) (via sym5 fix5 (by decide +kernel) (b2_241 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a189) (via sym6 fix6 (by decide +kernel) (b2_205 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_234) (b2_234 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a190) (via sym5 fix5 (by decide +kernel) (b2_268 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a191,a192,s2_235,a193]) (hints := [16902,10276,16902,0,18444,18500,18444,3,18436,18500,16902,1,18436,10276,18444,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a191,a192,s2_235,a193], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a191) (via sym5 fix5 (by decide +kernel) (b2_237 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a192) (via sym1 fix1 (by decide +kernel) (b2_204 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_235) (b2_235 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a193) (via sym5 fix5 (by decide +kernel) (b2_253 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a194,a195,s2_236,a196]) (hints := [33800,10276,33800,0,33808,51396,35856,3,33800,51396,33800,1,35848,10276,35856,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a194,a195,s2_236,a196], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a194) (via sym5 fix5 (by decide +kernel) (b2_243 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a195) (via sym5 fix5 (by decide +kernel) (b2_41 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_236) (b2_236 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a196) (via sym5 fix5 (by decide +kernel) (b2_273 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a197,a198,s2_227,s2_226,a199,a200]) (hints := [20550,20550,41094,0,28774,28774,4,5,28774,28774,41094,1,20550,20550,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [a197,a198,s2_227,s2_226,a199,a200], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a197) (via sym5 fix5 (by decide +kernel) (b2_255 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a198) (via sym6 fix6 (by decide +kernel) (b2_48 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_227) (b2_227 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_226) (b2_226 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a199) (via sym5 fix5 (by decide +kernel) (b2_278 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a200) (via sym5 fix5 (by decide +kernel) (b2_270 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a201,a202,s2_228,a203]) (hints := [16902,36996,16902,0,20500,20548,20500,3,20484,20548,16902,1,20484,36996,20500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a201,a202,s2_228,a203], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a201) (via sym5 fix5 (by decide +kernel) (b2_246 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a202) (via sym3 fix3 (by decide +kernel) (b2_206 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_228) (b2_228 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a203) (via sym5 fix5 (by decide +kernel) (b2_260 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a204,a205,s2_229,a206]) (hints := [33800,20548,33800,0,36884,36996,36884,3,36868,36996,33800,1,36868,20548,36884,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a204,a205,s2_229,a206], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a204) (via sym5 fix5 (by decide +kernel) (b2_256 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a205) (via sym5 fix5 (by decide +kernel) (b2_203 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_229) (b2_229 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a206) (via sym5 fix5 (by decide +kernel) (b2_275 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a207,a208,a209,a210]) (hints := [16902,41092,16902,0,25126,57540,25126,3,16902,57540,16902,1,25126,41092,25126,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a207,a208,a209,a210], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a207) (via sym5 fix5 (by decide +kernel) (b2_248 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a208) (via sym1 fix1 (by decide +kernel) (b2_79 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a209) (via sym6 fix6 (by decide +kernel) (b2_89 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a210) (via sym5 fix5 (by decide +kernel) (b2_269 theta)) <|
    PetersenLocalChildren.nil
private theorem pair1_3_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s2_267,s2_266,s2_277,s2_276,a211,s2_220,s2_221]) (hints := [33803,0,33803,1,41095,41095,2,3,40967,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [s2_267,s2_266,s2_277,s2_276,a211,s2_220,s2_221], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_267) (b2_267 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_266) (b2_266 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_277) (b2_277 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_276) (b2_276 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a211) (via sym2 fix2 (by decide +kernel) (b2_220 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_220) (b2_220 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := s2_221) (b2_221 theta) <|
    PetersenLocalChildren.nil
private theorem pair1_3_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 10 s1_3 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a212,a213,a214,a215]) (hints := [16902,16902,33800,0,33864,49798,50248,3,49670,49798,33800,1,16902,16902,50248,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a212,a213,a214,a215], Blocked tgt 10 V
  exact PetersenLocalChildren.push (P := Blocked tgt 10) (x := a212) (via sym5 fix5 (by decide +kernel) (b2_250 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a213) (via sym5 fix5 (by decide +kernel) (b2_77 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a214) (via sym3 fix3 (by decide +kernel) (b2_115 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 10) (x := a215) (via sym5 fix5 (by decide +kernel) (b2_274 theta)) <|
    PetersenLocalChildren.nil
theorem b1_3 (theta : Extra1020K12.Theta) : Blocked tgt 11 s1_3 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xffffffff00000000ffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa),(0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xffffffff00000000ffffffff00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xffffffff00000000ffffffff00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xffffffff00000000ffffffff00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 10 s1_3 pair
  exact PetersenLocalChildren.push (pair1_3_0 theta) <|
    PetersenLocalChildren.push (pair1_3_1 theta) <|
    PetersenLocalChildren.push (pair1_3_2 theta) <|
    PetersenLocalChildren.push (pair1_3_3 theta) <|
    PetersenLocalChildren.push (pair1_3_4 theta) <|
    PetersenLocalChildren.push (pair1_3_5 theta) <|
    PetersenLocalChildren.push (pair1_3_6 theta) <|
    PetersenLocalChildren.push (pair1_3_7 theta) <|
    PetersenLocalChildren.push (pair1_3_8 theta) <|
    PetersenLocalChildren.push (pair1_3_9 theta) <|
    PetersenLocalChildren.push (pair1_3_10 theta) <|
    PetersenLocalChildren.push (pair1_3_11 theta) <|
    PetersenLocalChildren.push (pair1_3_12 theta) <|
    PetersenLocalChildren.push (pair1_3_13 theta) <|
    PetersenLocalChildren.push (pair1_3_14 theta) <|
    PetersenLocalChildren.push (pair1_3_15 theta) <|
    PetersenLocalChildren.push (pair1_3_16 theta) <|
    PetersenLocalChildren.push (pair1_3_17 theta) <|
    PetersenLocalChildren.push (pair1_3_18 theta) <|
    PetersenLocalChildren.push (pair1_3_19 theta) <|
    PetersenLocalChildren.push (pair1_3_20 theta) <|
    PetersenLocalChildren.push (pair1_3_21 theta) <|
    PetersenLocalChildren.push (pair1_3_22 theta) <|
    PetersenLocalChildren.push (pair1_3_23 theta) <|
    PetersenLocalChildren.push (pair1_3_24 theta) <|
    PetersenLocalChildren.push (pair1_3_25 theta) <|
    PetersenLocalChildren.push (pair1_3_26 theta) <|
    PetersenLocalChildren.push (pair1_3_27 theta) <|
    PetersenLocalChildren.push (pair1_3_28 theta) <|
    PetersenLocalChildren.push (pair1_3_29 theta) <|
    PetersenLocalChildren.push (pair1_3_30 theta) <|
    PetersenLocalChildren.push (pair1_3_31 theta) <|
    PetersenLocalChildren.push (pair1_3_32 theta) <|
    PetersenLocalChildren.push (pair1_3_33 theta) <|
    PetersenLocalChildren.push (pair1_3_34 theta) <|
    PetersenLocalChildren.push (pair1_3_35 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
