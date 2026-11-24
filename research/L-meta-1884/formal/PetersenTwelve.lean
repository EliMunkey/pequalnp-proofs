import PetersenPairMinor
import PetersenPathFour

open PetersenMinor PetersenPairMinor PetersenSignedBridge PetersenWordCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenTwelve

def layout : Fin 5 → Fin 10 → Bool ⊕ Fin 4 := ![![.inr 0,.inr 1,.inr 2,.inr 3,.inl false,.inl false,.inl false,.inl false,.inl false,.inl false],![.inl false,.inl false,.inl false,.inl false,.inr 0,.inr 3,.inl false,.inr 2,.inl false,.inr 1],![.inr 0,.inl false,.inl false,.inl false,.inl false,.inr 1,.inr 3,.inl false,.inr 2,.inl false],![.inl false,.inr 1,.inr 0,.inl false,.inl false,.inl false,.inr 2,.inl false,.inr 3,.inl false],![.inr 0,.inl false,.inl false,.inr 2,.inr 1,.inl false,.inl false,.inl false,.inr 3,.inl false]]
def choice : Fin 10 → Fin 10 → Fin 5 := ![![0,1,1,1,3,3,1,3,1,3],![1,0,1,1,2,4,1,2,1,2],![1,1,0,1,2,4,1,2,1,2],![1,1,1,0,2,3,1,2,1,2],![3,2,2,2,0,0,0,0,0,0],![3,4,4,3,0,0,0,0,0,0],![1,1,1,1,0,0,0,0,0,0],![3,2,2,2,0,0,0,0,0,0],![1,1,1,1,0,0,0,0,0,0],![3,2,2,2,0,0,0,0,0,0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem lookup : ∀ i j : Fin 10, i ≠ j →
  (layout (choice i j) i).isLeft ∧ (layout (choice i j) j).isLeft := by decide

private theorem nfixed : ∀ q : Fin 5, (fixed (layout q)).card = 6 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem row_check : ∀ (q : Fin 5) (v : Fin 16),
    PetersenTarget (rowMap (layout q) v) = read PetersenPathFour.target v := by decide

private theorem nonconst : ¬ ∃ b, read PetersenPathFour.target = fun _ => b := by
  rintro ⟨b,h⟩
  have u := congrFun h 0
  have v := congrFun h 3
  change false = b at u
  change true = b at v
  simp_all

theorem binary_lower {k W} (src : Run base k W) (out : Av W PetersenTarget) : 12 ≤ k := by
  have small : NoAtMost (inputs 4) PetersenPathFour.target 3 := by
    have h : inputs 4 = PetersenPathFour.input := by decide
    rw [h]
    exact PetersenPathFour.no_three_gates
  apply pair_lift (n := 4) PetersenPathFour.target nonconst small (d := 6) _ src out
  intro i j ne
  obtain ⟨left,right⟩ := lookup i j ne
  exact ⟨layout (choice i j),left,right,le_of_eq (nfixed _).symm,funext (row_check _)⟩

theorem public_lower (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) :
    12 ≤ C.size := by
  obtain ⟨W,r,o⟩ := signed_realization C σ u fan
  rw [funext computes] at o
  exact (binary_lower r o).trans (List.length_filter_le ..)

#print axioms binary_lower
#print axioms public_lower

end PetersenTwelve
