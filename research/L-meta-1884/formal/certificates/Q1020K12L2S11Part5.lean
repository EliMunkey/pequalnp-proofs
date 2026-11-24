import PetersenLocalChildren
import Q1020K12L2S11Local
import Q1020K12L3S0
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S13
import Q1020K12L3S20
import Q1020K12L3S23
import Q1020K12L3S30
import Q1020K12L3S32
import Q1020K12L3S39
import Q1020K12L3S40
import Q1020K12L3S44
import Q1020K12L3S45
import Q1020K12L3S46
import Q1020K12L3S49
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S60
import Q1020K12L3S63
import Q1020K12L3S66
import Q1020K12L3S68
import Q1020K12L3S70
import Q1020K12L3S71
import Q1020K12L3S74
import Q1020K12L3S75
import Q1020K12L3S77
import Q1020K12L3S79
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S11Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
private theorem pair2_487_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_2334,a2128,a2129,s3_3113]) (hints := [774,774,0,8998,8998,3,8998,8998,1,774,774,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_2334,a2128,a2129,s3_3113], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2334) (b3_2334 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2128) (via sym4 fix4 (by decide +kernel) (b3_1697 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2129) (via sym6 fix6 (by decide +kernel) (b3_2072 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3113) (b3_3113 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1540,8480,1540,769,770,769,768,770,1540,768,8480,769]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,1538,8484,9508,34177,1538,9508,1538,770,770,34177]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10272,778,2826,18753,2818,2826,10272,770,770,18753]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,20544,786,4882,20801,4866,4882,20544,770,770,20801]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,41088,8480,8480,41345,8480,8480,41088,770,770,41345]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,16898,18441,24928,18697,16898,24928,16898,770,770,18697]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2130,s3_2981]) (hints := [772,772,40994,33668,33668,1,40994,33668,40994,772,772,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a2130,s3_2981], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2130) (via sym7 fix7 (by decide +kernel) (b3_1936 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2981) (b3_2981 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2131,s3_214,a2132,s3_2977]) (hints := [774,774,0,8484,8484,3,8484,8484,1,774,774,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a2131,s3_214,a2132,s3_2977], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2131) (via sym1 fix1 (by decide +kernel) (b3_2648 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_214) (b3_214 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2132) (via sym7 fix7 (by decide +kernel) (b3_2190 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2977) (b3_2977 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a784,s3_265,s3_253]) (hints := [772,0,772,9767,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a784,s3_265,s3_253], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a784) (via sym1 fix1 (by decide +kernel) (b3_19 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_265) (b3_265 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_253) (b3_253 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2133,a2134,a2135,a2136]) (hints := [1542,0,1542,9766,3,9766,1542,1,1542,9766,2,9766]) (by decide +kernel) ?_
  change ∀ V ∈ [a2133,a2134,a2135,a2136], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2133) (via sym2 fix2 (by decide +kernel) (b3_2334 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2134) (via sym5 fix5 (by decide +kernel) (b3_2072 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2135) (via sym7 fix7 (by decide +kernel) (b3_1697 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2136) (via sym2 fix2 (by decide +kernel) (b3_3113 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2137,a2138,a2139,s3_3191]) (hints := [10276,0,10276,10790,3,10790,10276,1,10276,10790,2,10790]) (by decide +kernel) ?_
  change ∀ V ∈ [a2137,a2138,a2139,s3_3191], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2137) (via sym5 fix5 (by decide +kernel) (b3_2542 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2138) (via sym2 fix2 (by decide +kernel) (b3_1849 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2139) (via sym4 fix4 (by decide +kernel) (b3_1696 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3191) (b3_3191 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2140,s3_1849,a2141,a2142]) (hints := [20548,0,20548,37510,3,37510,20548,1,20548,37510,2,37510]) (by decide +kernel) ?_
  change ∀ V ∈ [a2140,s3_1849,a2141,a2142], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2140) (via sym6 fix6 (by decide +kernel) (b3_2542 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1849) (b3_1849 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2141) (via sym7 fix7 (by decide +kernel) (b3_1696 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2142) (via sym2 fix2 (by decide +kernel) (b3_3191 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2143,a2144,a2145,a2146]) (hints := [41092,0,41092,41606,3,41606,41092,1,41092,41606,2,41606]) (by decide +kernel) ?_
  change ∀ V ∈ [a2143,a2144,a2145,a2146], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2143) (via sym1 fix1 (by decide +kernel) (b3_2796 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2144) (via sym2 fix2 (by decide +kernel) (b3_579 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2145) (via sym4 fix4 (by decide +kernel) (b3_967 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2146) (via sym1 fix1 (by decide +kernel) (b3_3250 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_2864,a2147,a2148,a2149]) (hints := [16902,0,16902,25126,3,25126,16902,1,16902,25126,2,25126]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_2864,a2147,a2148,a2149], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2864) (b3_2864 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2147) (via sym1 fix1 (by decide +kernel) (b3_1268 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2148) (via sym4 fix4 (by decide +kernel) (b3_1698 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2149) (via sym5 fix5 (by decide +kernel) (b3_3326 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a1057,s3_579,a2150,a2151]) (hints := [40996,0,40996,41510,3,41510,40996,1,40996,41510,2,41510]) (by decide +kernel) ?_
  change ∀ V ∈ [a1057,s3_579,a2150,a2151], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a1057) (via sym3 fix3 (by decide +kernel) (b3_2796 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_579) (b3_579 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2150) (via sym7 fix7 (by decide +kernel) (b3_967 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2151) (via sym3 fix3 (by decide +kernel) (b3_3250 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a784,s3_21,s3_12,a2152,a2153,a2154]) (hints := [1,0,2,3,4,5]) (by decide +kernel) ?_
  change ∀ V ∈ [a784,s3_21,s3_12,a2152,a2153,a2154], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a784) (via sym1 fix1 (by decide +kernel) (b3_19 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_21) (b3_21 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_12) (b3_12 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2152) (via sym4 fix4 (by decide +kernel) (b3_1673 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2153) (via sym4 fix4 (by decide +kernel) (b3_1667 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2154) (via sym4 fix4 (by decide +kernel) (b3_1666 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [769,769,33920,1538,1540,1538,1536,1540,33920,1536,769,1538]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [769,769,10272,777,2825,10786,2817,2825,10272,769,769,10786]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [769,769,20544,785,4881,37506,4865,4881,20544,769,769,37506]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2155,s3_2984]) (hints := [771,771,41090,41604,1,41604,41090,0,41090,771,771,41604]) (by decide +kernel) ?_
  change ∀ V ∈ [a2155,s3_2984], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2155) (via sym2 fix2 (by decide +kernel) (b3_860 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2984) (b3_2984 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [769,769,18440,16898,16960,16898,16896,16960,18440,16896,769,16898]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_860,a2156]) (hints := [771,771,40994,41508,1,41508,40994,0,40994,771,771,41508]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_860,a2156], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_860) (b3_860 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2156) (via sym2 fix2 (by decide +kernel) (b3_2984 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_253,a2154,s3_252,s3_251,s3_2986,s3_2985,s3_2978]) (hints := [4,5,6,2,0,3,776,776,1]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_253,a2154,s3_252,s3_251,s3_2986,s3_2985,s3_2978], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_253) (b3_253 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2154) (via sym4 fix4 (by decide +kernel) (b3_1666 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_252) (b3_252 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_251) (b3_251 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2986) (b3_2986 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2985) (b3_2985 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2978) (b3_2978 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,10272,1546,3594,11300,3586,3594,10272,1538,1538,11300]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,20544,1554,5650,21572,5634,5650,20544,1538,1538,21572]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2157,a2158]) (hints := [1540,1540,41090,9764,9764,1,9764,9764,41090,1540,1540,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a2157,a2158], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2157) (via sym4 fix4 (by decide +kernel) (b3_1936 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2158) (via sym2 fix2 (by decide +kernel) (b3_2981 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,16898,18444,50368,19468,16898,50368,16898,1538,1538,19468]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,40992,40996,33920,42020,40992,33920,40992,1538,1538,42020]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2159,a2160,a2161,a2162]) (hints := [1542,1542,0,9766,9766,3,9766,9766,1,1542,1542,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a2159,a2160,a2161,a2162], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2159) (via sym3 fix3 (by decide +kernel) (b3_2648 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2160) (via sym2 fix2 (by decide +kernel) (b3_214 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2161) (via sym4 fix4 (by decide +kernel) (b3_2190 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2162) (via sym2 fix2 (by decide +kernel) (b3_2977 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10272,10272,20544,10288,14384,39048,14368,14384,20544,10272,10272,39048]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [18496,18496,41088,10272,10272,43144,10272,10272,41088,18496,18496,43144]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,10272,16898,18440,18496,18440,18432,18496,16898,18432,10272,18440]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2163,s3_2982]) (hints := [10274,10274,40994,51394,51394,1,40994,51394,40994,10274,10274,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a2163,s3_2982], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2163) (via sym3 fix3 (by decide +kernel) (b3_1927 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2982) (b3_2982 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2164,a2165,a2166,s3_2979]) (hints := [18500,18500,0,10276,10276,3,10276,10276,1,18500,18500,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a2164,a2165,a2166,s3_2979], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2164) (via sym4 fix4 (by decide +kernel) (b3_2651 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2165) (via sym5 fix5 (by decide +kernel) (b3_216 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2166) (via sym3 fix3 (by decide +kernel) (b3_2187 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2979) (b3_2979 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2167,a2168]) (hints := [20546,20546,41090,28770,28770,1,28770,28770,41090,20546,20546,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a2167,a2168], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2167) (via sym1 fix1 (by decide +kernel) (b3_1927 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2168) (via sym2 fix2 (by decide +kernel) (b3_2982 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_36 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,36992,16898,20496,20544,20496,20480,20544,16898,20480,36992,20496]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_37 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [40992,20544,40992,41008,36992,45104,40992,36992,40992,45088,20544,45104]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_38 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2169,a2170,a2171,a2172]) (hints := [20548,20548,0,28772,28772,3,28772,28772,1,20548,20548,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a2169,a2170,a2171,a2172], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2169) (via sym7 fix7 (by decide +kernel) (b3_2651 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2170) (via sym6 fix6 (by decide +kernel) (b3_216 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2171) (via sym1 fix1 (by decide +kernel) (b3_2187 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2172) (via sym2 fix2 (by decide +kernel) (b3_2979 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_39 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,41088,16898,25122,57536,25122,16898,57536,16898,25122,41088,25122]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_40 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a2173,a2174,s3_1363,a2175]) (hints := [33832,0,1,41092,41092,2,40996,3,40996]) (by decide +kernel) ?_
  change ∀ V ∈ [a2173,a2174,s3_1363,a2175], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2173) (via sym3 fix3 (by decide +kernel) (b3_2870 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2174) (via sym1 fix1 (by decide +kernel) (b3_2870 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1363) (b3_1363 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2175) (via sym2 fix2 (by decide +kernel) (b3_1363 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_41 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_12,a2175,a2176]) (hints := [8452,41091,0,8452,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_12,a2175,a2176], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_12) (b3_12 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2175) (via sym2 fix2 (by decide +kernel) (b3_1363 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2176) (via sym2 fix2 (by decide +kernel) (b3_1362 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_487_42 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,16898,40992,41056,49794,57440,40992,49794,40992,16898,16898,57440]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_487_43 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_2972,a2177,a2178,s3_2980]) (hints := [16902,16902,0,25126,25126,3,25126,25126,1,16902,16902,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_2972,a2177,a2178,s3_2980], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2972) (b3_2972 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2177) (via sym5 fix5 (by decide +kernel) (b3_261 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2178) (via sym1 fix1 (by decide +kernel) (b3_1659 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2980) (b3_2980 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_487_44 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_487 (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_12,s3_1363,s3_1362]) (hints := [33799,40995,0,33799,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_12,s3_1363,s3_1362], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_12) (b3_12 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1363) (b3_1363 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1362) (b3_1362 theta) <|
    PetersenLocalChildren.nil
theorem b2_487 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_487 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccc00000000cccccccc00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000)], PetersenLocalChildren.PairOK tgt 9 s2_487 pair
  exact PetersenLocalChildren.push (pair2_487_0 theta) <|
    PetersenLocalChildren.push (pair2_487_1 theta) <|
    PetersenLocalChildren.push (pair2_487_2 theta) <|
    PetersenLocalChildren.push (pair2_487_3 theta) <|
    PetersenLocalChildren.push (pair2_487_4 theta) <|
    PetersenLocalChildren.push (pair2_487_5 theta) <|
    PetersenLocalChildren.push (pair2_487_6 theta) <|
    PetersenLocalChildren.push (pair2_487_7 theta) <|
    PetersenLocalChildren.push (pair2_487_8 theta) <|
    PetersenLocalChildren.push (pair2_487_9 theta) <|
    PetersenLocalChildren.push (pair2_487_10 theta) <|
    PetersenLocalChildren.push (pair2_487_11 theta) <|
    PetersenLocalChildren.push (pair2_487_12 theta) <|
    PetersenLocalChildren.push (pair2_487_13 theta) <|
    PetersenLocalChildren.push (pair2_487_14 theta) <|
    PetersenLocalChildren.push (pair2_487_15 theta) <|
    PetersenLocalChildren.push (pair2_487_16 theta) <|
    PetersenLocalChildren.push (pair2_487_17 theta) <|
    PetersenLocalChildren.push (pair2_487_18 theta) <|
    PetersenLocalChildren.push (pair2_487_19 theta) <|
    PetersenLocalChildren.push (pair2_487_20 theta) <|
    PetersenLocalChildren.push (pair2_487_21 theta) <|
    PetersenLocalChildren.push (pair2_487_22 theta) <|
    PetersenLocalChildren.push (pair2_487_23 theta) <|
    PetersenLocalChildren.push (pair2_487_24 theta) <|
    PetersenLocalChildren.push (pair2_487_25 theta) <|
    PetersenLocalChildren.push (pair2_487_26 theta) <|
    PetersenLocalChildren.push (pair2_487_27 theta) <|
    PetersenLocalChildren.push (pair2_487_28 theta) <|
    PetersenLocalChildren.push (pair2_487_29 theta) <|
    PetersenLocalChildren.push (pair2_487_30 theta) <|
    PetersenLocalChildren.push (pair2_487_31 theta) <|
    PetersenLocalChildren.push (pair2_487_32 theta) <|
    PetersenLocalChildren.push (pair2_487_33 theta) <|
    PetersenLocalChildren.push (pair2_487_34 theta) <|
    PetersenLocalChildren.push (pair2_487_35 theta) <|
    PetersenLocalChildren.push (pair2_487_36 theta) <|
    PetersenLocalChildren.push (pair2_487_37 theta) <|
    PetersenLocalChildren.push (pair2_487_38 theta) <|
    PetersenLocalChildren.push (pair2_487_39 theta) <|
    PetersenLocalChildren.push (pair2_487_40 theta) <|
    PetersenLocalChildren.push (pair2_487_41 theta) <|
    PetersenLocalChildren.push (pair2_487_42 theta) <|
    PetersenLocalChildren.push (pair2_487_43 theta) <|
    PetersenLocalChildren.push (pair2_487_44 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
