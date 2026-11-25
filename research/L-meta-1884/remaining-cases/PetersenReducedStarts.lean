import PetersenTenStarts
import HNC042Verified
import HMC010Verified
import HMC161RVerified
open PetersenWordCost PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenReducedStarts
structure Remaining : Prop where
  g1020_0_1_2 : NoAtMost ((0x4444444444444444444444444444444444444444444444444444444444444444 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_0_4_0 : NoAtMost ((0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_0_6_2 : NoAtMost ((0x5555555555555555000000000000000055555555555555550000000000000000 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_5_0 : NoAtMost ((0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_5_1 : NoAtMost ((0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_6_0 : NoAtMost ((0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12
  g1020_1_6_3 : NoAtMost ((0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000 : BitVec 256) :: inputs 8) 0xfffffffffffffffcfffffffffffff8f8ffffffeeffffffccffeaffeac8c8c8c8 12

theorem prior (h : Remaining) : PetersenTenStarts.Remaining where
  g1018_0_4_2 := NC042Cert.complete0_4_2
  g1020_0_1_0 := MC010Cert.complete0_1_0
  g1020_0_1_2 := h.g1020_0_1_2
  g1020_0_4_0 := h.g1020_0_4_0
  g1020_0_6_2 := h.g1020_0_6_2
  g1020_1_5_0 := h.g1020_1_5_0
  g1020_1_5_1 := h.g1020_1_5_1
  g1020_1_6_0 := h.g1020_1_6_0
  g1020_1_6_1 := MC161RCert.complete1_6_1
  g1020_1_6_3 := h.g1020_1_6_3
theorem original (h : Remaining) (pure : PetersenThreeChecks.Pure) (shared : PetersenShared22.Hard 15)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool) (fan : FanInTwo C) (small : C.size≤18) :
    ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x :=
  PetersenTenStarts.original (prior h) pure shared C σ u fan small
#print axioms original
end PetersenReducedStarts
