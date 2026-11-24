import PetersenLocalChildren
import Q1020K12L2S12Local
import Q1020K12L3S0
import Q1020K12L3S5
import Q1020K12L3S6
import Q1020K12L3S33
import Q1020K12L3S34
import Q1020K12L3S37
import Q1020K12L3S38
import Q1020K12L3S39
import Q1020K12L3S40
import Q1020K12L3S46
import Q1020K12L3S52
import Q1020K12L3S55
import Q1020K12L3S63
import Q1020K12L3S64
import Q1020K12L3S69
import Q1020K12L3S70
import Q1020K12L3S71
import Q1020K12L3S79
import Q1020K12L3S80
open PetersenWordCost PetersenPackedPin PetersenLayerCheck PetersenSymmetry
open Q1020Symmetry
namespace Orbits1020Cost12
open Q1020K12L2S12Local
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option maxHeartbeats 0
theorem b2_524 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_524 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(6,true))] s2_524 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffff0000ffff0000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons pc26w31 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons stored0 rfl))))))))) (by decide +kernel)
theorem b2_525 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_525 := by
  intro m le c
  apply rejects_sound extra30 i7 10 tgt (small30 theta) hot30 [(false,(3,true),(0,true))] s2_525 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffaaffaaffaaffaaffaaffaaffaaffaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000] (PetersenWireProjection.cons stored15 (PetersenWireProjection.cons stored14 (PetersenWireProjection.cons stored13 (PetersenWireProjection.cons stored12 (PetersenWireProjection.cons stored11 (PetersenWireProjection.cons stored10 (PetersenWireProjection.cons pc30w40 (PetersenWireProjection.cons stored9 (PetersenWireProjection.cons stored8 rfl))))))))) (by decide +kernel)
theorem b2_526 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_526 := by
  intro m le c
  apply rejects_sound extra34 i7 10 tgt (small34 theta) hot34 [(false,(0,true),(2,true))] s2_526 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0xcccccccccccccccccccccccccccccccc,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000,0xff00ff00ff00ff00ff00ff00ff00ff00,0x0,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfafafafafafafafafafafafafafafafa,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000] (PetersenWireProjection.cons stored23 (PetersenWireProjection.cons stored22 (PetersenWireProjection.cons stored21 (PetersenWireProjection.cons stored20 (PetersenWireProjection.cons stored19 (PetersenWireProjection.cons stored18 (PetersenWireProjection.cons pc34w44 (PetersenWireProjection.cons stored17 (PetersenWireProjection.cons stored16 rfl))))))))) (by decide +kernel)
theorem b2_527 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_527 := by
  intro m le c
  apply rejects_sound extra26 i7 10 tgt (small26 theta) hot26 [(false,(4,true),(0,true))] s2_527 10 _ le
  exact PetersenWireProjection.reuse _ _ _ _ _ _ [0x0,0xffff0000ffff0000ffff0000ffff0000,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000,0xcccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xffffaaaaffffaaaaffffaaaaffffaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0] (PetersenWireProjection.cons stored7 (PetersenWireProjection.cons stored6 (PetersenWireProjection.cons stored5 (PetersenWireProjection.cons stored4 (PetersenWireProjection.cons stored3 (PetersenWireProjection.cons stored2 (PetersenWireProjection.cons stored1 (PetersenWireProjection.cons pc26w54 (PetersenWireProjection.cons pc26w53 (PetersenWireProjection.cons stored0 rfl)))))))))) (by decide +kernel)
private theorem pair2_528_0 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [8480,8480,16960,770,770,17217,770,770,16960,8480,8480,17217]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_1 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,1538,8484,9508,34177,1538,9508,1538,770,770,34177]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_2 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10272,778,2826,18753,2818,2826,10272,770,770,18753]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_3 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,20544,786,4882,20801,4866,4882,20544,770,770,20801]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_4 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,10762,8480,8480,24897,8962,8480,10762,770,770,24897]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_5 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3222,a3223]) (hints := [772,772,16900,24930,24930,1,16900,24930,16900,772,772,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a3222,a3223], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3222) (via sym6 fix6 (by decide +kernel) (b3_1944 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3223) (via sym1 fix1 (by decide +kernel) (b3_3377 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_6 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_2654,a3224,a3225,s3_3344]) (hints := [8484,8484,0,774,774,3,774,774,1,8484,8484,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_2654,a3224,a3225,s3_3344], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2654) (b3_2654 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3224) (via sym1 fix1 (by decide +kernel) (b3_222 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3225) (via sym6 fix6 (by decide +kernel) (b3_2198 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3344) (b3_3344 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_528_7 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_2690,s3_2689,s3_2683,a3226,a3227,a3228,a3229,s3_3331]) (hints := [0,1,2,778,778,7,778,778,3,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_2690,s3_2689,s3_2683,a3226,a3227,a3228,a3229,s3_3331], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2690) (b3_2690 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2689) (b3_2689 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2683) (b3_2683 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3226) (via sym3 fix3 (by decide +kernel) (b3_37 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3227) (via sym6 fix6 (by decide +kernel) (b3_2319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3228) (via sym6 fix6 (by decide +kernel) (b3_2320 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3229) (via sym6 fix6 (by decide +kernel) (b3_2314 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3331) (b3_3331 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_528_8 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [770,770,33796,33797,33666,34053,33538,33666,33796,770,770,34053]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_9 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16960,16960,33920,1538,17988,1538,17984,17988,33920,1538,16960,1538]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_10 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3230,a3231]) (hints := [10274,16962,10274,10788,1,10788,10274,0,10274,10788,16962,10788]) (by decide +kernel) ?_
  change ∀ V ∈ [a3230,a3231], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3230) (via sym2 fix2 (by decide +kernel) (b3_1944 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3231) (via sym4 fix4 (by decide +kernel) (b3_3377 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_11 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_1939,a3232]) (hints := [16962,16962,20546,37508,1,37508,20546,0,20546,16962,16962,37508]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_1939,a3232], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1939) (b3_1939 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3232) (via sym7 fix7 (by decide +kernel) (b3_3379 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_12 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16960,16960,24897,10762,25184,10762,25152,25184,24897,10762,16960,10762]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_13 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3233,s3_2899,a3234,a3235]) (hints := [18446,0,1,16964,16964,2,16902,3,16902]) (by decide +kernel) ?_
  change ∀ V ∈ [a3233,s3_2899,a3234,a3235], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3233) (via sym5 fix5 (by decide +kernel) (b3_2899 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2899) (b3_2899 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3234) (via sym1 fix1 (by decide +kernel) (b3_1435 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3235) (via sym4 fix4 (by decide +kernel) (b3_1435 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_14 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3235,s3_20,a3236]) (hints := [9767,16963,1,9767,0,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3235,s3_20,a3236], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3235) (via sym4 fix4 (by decide +kernel) (b3_1435 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_20) (b3_20 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3236) (via sym4 fix4 (by decide +kernel) (b3_1425 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_15 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_19,a3237,a3238,a3239]) (hints := [16964,16964,0,1,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_19,a3237,a3238,a3239], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3237) (via sym4 fix4 (by decide +kernel) (b3_1597 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3238) (via sym4 fix4 (by decide +kernel) (b3_1598 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3239) (via sym4 fix4 (by decide +kernel) (b3_1592 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_16 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,16960,33796,37394,49856,37394,33796,49856,33796,37394,16960,37394]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_17 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,10272,1546,3594,11300,3586,3594,10272,1538,1538,11300]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_18 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,20544,1554,5650,21572,5634,5650,20544,1538,1538,21572]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_19 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,10762,1570,9762,25925,9730,9762,10762,1538,1538,25925]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_20 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3240,a3241]) (hints := [1540,1540,16900,50370,50370,1,16900,50370,16900,1540,1540,0]) (by decide +kernel) ?_
  change ∀ V ∈ [a3240,a3241], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3240) (via sym5 fix5 (by decide +kernel) (b3_1939 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3241) (via sym3 fix3 (by decide +kernel) (b3_3379 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_21 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3242,a3243,a3244,a3245]) (hints := [33924,33924,0,1542,1542,3,1542,1542,1,33924,33924,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3242,a3243,a3244,a3245], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3242) (via sym2 fix2 (by decide +kernel) (b3_2659 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3243) (via sym3 fix3 (by decide +kernel) (b3_224 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3244) (via sym5 fix5 (by decide +kernel) (b3_2193 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3245) (via sym2 fix2 (by decide +kernel) (b3_3346 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_22 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3246,a3247,a3248,s3_3332]) (hints := [33924,33924,0,1542,1542,3,1542,1542,1,33924,33924,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3246,a3247,a3248,s3_3332], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3246) (via sym2 fix2 (by decide +kernel) (b3_2705 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3247) (via sym3 fix3 (by decide +kernel) (b3_26 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3248) (via sym5 fix5 (by decide +kernel) (b3_2220 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3332) (b3_3332 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_528_23 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [1538,1538,36880,33796,33920,33796,33792,33920,36880,33792,1538,33796]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_24 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10272,10272,20544,10288,14384,39048,14368,14384,20544,10272,10272,39048]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_25 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [18496,18496,24897,10762,10272,10762,10754,10272,24897,10754,18496,10762]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_26 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,10272,16898,16906,18496,18954,16898,18496,16898,18946,10272,18954]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_27 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3249,a3250,a3251,a3252]) (hints := [10276,10276,0,10790,10790,3,10790,10790,1,10276,10276,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3249,a3250,a3251,a3252], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3249) (via sym5 fix5 (by decide +kernel) (b3_2654 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3250) (via sym4 fix4 (by decide +kernel) (b3_222 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3251) (via sym2 fix2 (by decide +kernel) (b3_2198 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3252) (via sym5 fix5 (by decide +kernel) (b3_3344 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_28 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3253,a3254,a3255,a3256,a3257,a3258,a3259,a3260]) (hints := [0,1,2,10280,10280,7,10280,10280,3,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [a3253,a3254,a3255,a3256,a3257,a3258,a3259,a3260], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3253) (via sym5 fix5 (by decide +kernel) (b3_2690 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3254) (via sym5 fix5 (by decide +kernel) (b3_2689 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3255) (via sym5 fix5 (by decide +kernel) (b3_2683 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3256) (via sym7 fix7 (by decide +kernel) (b3_37 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3257) (via sym2 fix2 (by decide +kernel) (b3_2319 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3258) (via sym2 fix2 (by decide +kernel) (b3_2320 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3259) (via sym2 fix2 (by decide +kernel) (b3_2314 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3260) (via sym5 fix5 (by decide +kernel) (b3_3331 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_29 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,10272,33796,33804,51392,35852,33796,51392,33796,35844,10272,35852]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_30 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [10762,20544,10762,10778,28768,14874,10762,28768,10762,14858,20544,14874]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_31 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,36992,16898,16914,20544,21010,16898,20544,16898,20994,36992,21010]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_32 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3261,a3262,s3_2193,a3263]) (hints := [36996,36996,0,20548,20548,3,20548,20548,1,36996,36996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3261,a3262,s3_2193,a3263], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3261) (via sym6 fix6 (by decide +kernel) (b3_2659 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3262) (via sym7 fix7 (by decide +kernel) (b3_224 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2193) (b3_2193 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3263) (via sym6 fix6 (by decide +kernel) (b3_3346 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_33 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3264,a3265,s3_2220,a3266]) (hints := [36996,36996,0,20548,20548,3,20548,20548,1,36996,36996,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3264,a3265,s3_2220,a3266], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3264) (via sym6 fix6 (by decide +kernel) (b3_2705 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3265) (via sym7 fix7 (by decide +kernel) (b3_26 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_2220) (b3_2220 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3266) (via sym5 fix5 (by decide +kernel) (b3_3332 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_34 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,20544,33796,36880,36992,36880,36864,36992,33796,36864,20544,36880]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_35 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,10762,16898,16930,24897,25122,16898,24897,16898,25090,10762,25122]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_36 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3267,a3268,a3269,a3270,a3271,a3272,a3273]) (hints := [0,1,2,10769,10769,3,4,5,6]) (by decide +kernel) ?_
  change ∀ V ∈ [a3267,a3268,a3269,a3270,a3271,a3272,a3273], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3267) (via sym1 fix1 (by decide +kernel) (b3_2986 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3268) (via sym1 fix1 (by decide +kernel) (b3_2985 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3269) (via sym1 fix1 (by decide +kernel) (b3_2978 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3270) (via sym1 fix1 (by decide +kernel) (b3_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3271) (via sym2 fix2 (by decide +kernel) (b3_1681 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3272) (via sym2 fix2 (by decide +kernel) (b3_1669 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3273) (via sym2 fix2 (by decide +kernel) (b3_1678 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_37 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_19,a3272,a3274]) (hints := [8452,10765,0,8452,1,2]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_19,a3272,a3274], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3272) (via sym2 fix2 (by decide +kernel) (b3_1669 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3274) (via sym2 fix2 (by decide +kernel) (b3_1667 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_38 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [33796,10762,33796,40992,41602,40992,41474,41602,33796,41474,10762,40992]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_39 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3234,s3_20,a3275]) (hints := [16901,16901,1,28723,0,2]) (by decide +kernel) ?_
  change ∀ V ∈ [a3234,s3_20,a3275], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3234) (via sym1 fix1 (by decide +kernel) (b3_1435 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_20) (b3_20 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3275) (via sym1 fix1 (by decide +kernel) (b3_1425 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_40 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_19,a2863,a3276,a2864]) (hints := [16902,16902,0,1,2,3]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_19,a2863,a3276,a2864], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2863) (via sym1 fix1 (by decide +kernel) (b3_1597 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3276) (via sym1 fix1 (by decide +kernel) (b3_1598 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2864) (via sym1 fix1 (by decide +kernel) (b3_1592 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_41 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[]) (hints := [16898,16898,33796,50244,49794,50244,49666,49794,33796,16898,16898,50244]) (by decide +kernel) ?_
  exact PetersenLocalChildren.nil
private theorem pair2_528_42 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc) := by
  refine PetersenLocalChildren.pair_close (bank := #[s3_20,s3_19,a3270,s3_21,a2424,a2867]) (hints := [3,0,1,4,2,5]) (by decide +kernel) ?_
  change ∀ V ∈ [s3_20,s3_19,a3270,s3_21,a2424,a2867], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_20) (b3_20 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_19) (b3_19 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3270) (via sym1 fix1 (by decide +kernel) (b3_267 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_21) (b3_21 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2424) (via sym1 fix1 (by decide +kernel) (b3_264 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a2867) (via sym1 fix1 (by decide +kernel) (b3_265 theta)) <|
    PetersenLocalChildren.nil
private theorem pair2_528_43 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3277,s3_1672,a3278,s3_3353]) (hints := [33800,0,33800,37398,3,37398,33800,1,33800,37398,2,37398]) (by decide +kernel) ?_
  change ∀ V ∈ [a3277,s3_1672,a3278,s3_3353], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3277) (via sym3 fix3 (by decide +kernel) (b3_2980 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1672) (b3_1672 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3278) (via sym3 fix3 (by decide +kernel) (b3_269 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3353) (b3_3353 theta) <|
    PetersenLocalChildren.nil
private theorem pair2_528_44 (theta : Extra1020K12.Theta) : PetersenLocalChildren.PairOK tgt 9 s2_528 (0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  refine PetersenLocalChildren.pair_close (bank := #[a3279,s3_1686,a3280,s3_3337]) (hints := [33800,0,33800,37398,3,37398,33800,1,33800,37398,2,37398]) (by decide +kernel) ?_
  change ∀ V ∈ [a3279,s3_1686,a3280,s3_3337], Blocked tgt 9 V
  exact PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3279) (via sym3 fix3 (by decide +kernel) (b3_2990 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_1686) (b3_1686 theta) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := a3280) (via sym3 fix3 (by decide +kernel) (b3_33 theta)) <|
    PetersenLocalChildren.push (P := Blocked tgt 9) (x := s3_3337) (b3_3337 theta) <|
    PetersenLocalChildren.nil
theorem b2_528 (theta : Extra1020K12.Theta) : Blocked tgt 10 s2_528 := by
  refine PetersenLocalChildren.finish (by decide +kernel) ?_
  change ∀ pair ∈ [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc),(0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000),(0xffffffffffffffffffffffffccccccccffffffffffffffffffffffffcccccccc,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000)], PetersenLocalChildren.PairOK tgt 9 s2_528 pair
  exact PetersenLocalChildren.push (pair2_528_0 theta) <|
    PetersenLocalChildren.push (pair2_528_1 theta) <|
    PetersenLocalChildren.push (pair2_528_2 theta) <|
    PetersenLocalChildren.push (pair2_528_3 theta) <|
    PetersenLocalChildren.push (pair2_528_4 theta) <|
    PetersenLocalChildren.push (pair2_528_5 theta) <|
    PetersenLocalChildren.push (pair2_528_6 theta) <|
    PetersenLocalChildren.push (pair2_528_7 theta) <|
    PetersenLocalChildren.push (pair2_528_8 theta) <|
    PetersenLocalChildren.push (pair2_528_9 theta) <|
    PetersenLocalChildren.push (pair2_528_10 theta) <|
    PetersenLocalChildren.push (pair2_528_11 theta) <|
    PetersenLocalChildren.push (pair2_528_12 theta) <|
    PetersenLocalChildren.push (pair2_528_13 theta) <|
    PetersenLocalChildren.push (pair2_528_14 theta) <|
    PetersenLocalChildren.push (pair2_528_15 theta) <|
    PetersenLocalChildren.push (pair2_528_16 theta) <|
    PetersenLocalChildren.push (pair2_528_17 theta) <|
    PetersenLocalChildren.push (pair2_528_18 theta) <|
    PetersenLocalChildren.push (pair2_528_19 theta) <|
    PetersenLocalChildren.push (pair2_528_20 theta) <|
    PetersenLocalChildren.push (pair2_528_21 theta) <|
    PetersenLocalChildren.push (pair2_528_22 theta) <|
    PetersenLocalChildren.push (pair2_528_23 theta) <|
    PetersenLocalChildren.push (pair2_528_24 theta) <|
    PetersenLocalChildren.push (pair2_528_25 theta) <|
    PetersenLocalChildren.push (pair2_528_26 theta) <|
    PetersenLocalChildren.push (pair2_528_27 theta) <|
    PetersenLocalChildren.push (pair2_528_28 theta) <|
    PetersenLocalChildren.push (pair2_528_29 theta) <|
    PetersenLocalChildren.push (pair2_528_30 theta) <|
    PetersenLocalChildren.push (pair2_528_31 theta) <|
    PetersenLocalChildren.push (pair2_528_32 theta) <|
    PetersenLocalChildren.push (pair2_528_33 theta) <|
    PetersenLocalChildren.push (pair2_528_34 theta) <|
    PetersenLocalChildren.push (pair2_528_35 theta) <|
    PetersenLocalChildren.push (pair2_528_36 theta) <|
    PetersenLocalChildren.push (pair2_528_37 theta) <|
    PetersenLocalChildren.push (pair2_528_38 theta) <|
    PetersenLocalChildren.push (pair2_528_39 theta) <|
    PetersenLocalChildren.push (pair2_528_40 theta) <|
    PetersenLocalChildren.push (pair2_528_41 theta) <|
    PetersenLocalChildren.push (pair2_528_42 theta) <|
    PetersenLocalChildren.push (pair2_528_43 theta) <|
    PetersenLocalChildren.push (pair2_528_44 theta) <|
    PetersenLocalChildren.nil
end Orbits1020Cost12
