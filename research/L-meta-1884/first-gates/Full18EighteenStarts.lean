import Full18SymConditional
import M189StartLabeled
import first8.FirstGateSurvey
open PetersenWordCost PetersenLayerCheck PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Full18
set_option maxRecDepth 200000
set_option maxHeartbeats 0
structure RemainingStarts : Prop where
  g191_0_2_1 : NoAtMost ((0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_0_2_3 : NoAtMost ((0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0 : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_0_3_1 : NoAtMost ((0xaa00aa00aa00aa00aa00aa00aa00aa : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_0_3_3 : NoAtMost ((0xaa00aa00aa00aa00aa00aa00aa00aa00 : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_0_4_0 : NoAtMost ((0xffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_0_4_1 : NoAtMost ((0xaaaa0000aaaa0000aaaa0000aaaa : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_3_4_0 : NoAtMost ((0xffffff00ffffff00ffffff00ffffff00 : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g191_3_5_0 : NoAtMost ((0xffffffffff00ff00ffffffffff00ff00 : BitVec 128) :: inputs 7) 0xfffffffffffaf8f8ffeafaeaffeaf8c8 10
  g1018_0_4_2 : NoAtMost ((0x5555000055550000555500005555000055550000555500005555000055550000 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff0f0ffffffccffffffccffeaffc0eaeac0c0 11
  g1020_0_1_0 : NoAtMost ((0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_0_1_2 : NoAtMost ((0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_0_4_0 : NoAtMost ((0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_0_6_2 : NoAtMost ((0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_5_0 : NoAtMost ((0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_5_1 : NoAtMost ((0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_6_0 : NoAtMost ((0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_6_1 : NoAtMost ((0xcccccccccccccccc0000000000000000cccccccccccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_6_3 : NoAtMost ((0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12

theorem from_remaining_starts (h : RemainingStarts) : Needs where
  g189_0_1_0 := PetersenSmallStarts.M189.all_forbidden _ (by decide +kernel)
  g189_0_1_1 := PetersenSmallStarts.M189.all_forbidden _ (by decide +kernel)
  g191_0_2_1 := h.g191_0_2_1
  g191_0_2_3 := h.g191_0_2_3
  g191_0_3_1 := h.g191_0_3_1
  g191_0_3_3 := h.g191_0_3_3
  g191_0_4_0 := h.g191_0_4_0
  g191_0_4_1 := h.g191_0_4_1
  g191_3_4_0 := h.g191_3_4_0
  g191_3_5_0 := h.g191_3_5_0
  g1018_0_4_2 := h.g1018_0_4_2
  g1020_0_1_0 := h.g1020_0_1_0
  g1020_0_1_2 := h.g1020_0_1_2
  g1020_0_4_0 := h.g1020_0_4_0
  g1020_0_6_1 := PetersenEightStarts.F0_6_1
  g1020_0_6_2 := h.g1020_0_6_2
  g1020_0_6_3 := PetersenEightStarts.F0_6_3
  g1020_1_5_0 := h.g1020_1_5_0
  g1020_1_5_1 := h.g1020_1_5_1
  g1020_1_6_0 := h.g1020_1_6_0
  g1020_1_6_1 := h.g1020_1_6_1
  g1020_1_6_3 := h.g1020_1_6_3

theorem eighteen_of_starts (h : RemainingStarts) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 18 ≤ C.size :=
  symmetry_public (from_remaining_starts h) C σ u fan computes
#print axioms eighteen_of_starts
end Full18
