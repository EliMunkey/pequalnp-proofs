import PetersenPairMinor
import PetersenCycleFive

open PetersenMinor PetersenPairMinor PetersenSignedBridge PetersenWordCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenFourteen

def layout : Fin 7 → Fin 10 → Bool ⊕ Fin 5 := ![![.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inl false,.inl false,.inl false,.inl false,.inl false],![.inl false,.inl false,.inl false,.inl false,.inl false,.inr 0,.inr 3,.inr 1,.inr 4,.inr 2],![.inr 0,.inr 1,.inr 2,.inl false,.inl false,.inr 4,.inl false,.inr 3,.inl false,.inl false],![.inr 0,.inl false,.inl false,.inr 2,.inr 1,.inr 4,.inl false,.inl false,.inr 3,.inl false],![.inl false,.inr 0,.inr 1,.inr 2,.inl false,.inl false,.inr 4,.inl false,.inr 3,.inl false],![.inr 0,.inr 1,.inl false,.inl false,.inr 4,.inl false,.inr 2,.inl false,.inl false,.inr 3],![.inl false,.inl false,.inr 0,.inr 1,.inr 2,.inl false,.inl false,.inr 4,.inl false,.inr 3]]
def choice : Fin 10 → Fin 10 → Fin 7 := ![![0,1,1,1,1,4,6,4,6,4],![1,0,1,1,1,6,3,3,6,3],![1,1,0,1,1,5,3,3,5,3],![1,1,1,0,1,5,2,5,2,2],![1,1,1,1,0,4,2,4,2,2],![4,6,5,5,4,0,0,0,0,0],![6,3,3,2,2,0,0,0,0,0],![4,3,3,5,4,0,0,0,0,0],![6,6,5,2,2,0,0,0,0,0],![4,3,3,2,2,0,0,0,0,0]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem lookup : ∀ i j : Fin 10, i ≠ j →
  (layout (choice i j) i).isLeft ∧ (layout (choice i j) j).isLeft := by decide

private theorem nfixed : ∀ q : Fin 7, (fixed (layout q)).card = 5 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem row_check : ∀ (q : Fin 7) (v : Fin 32),
    PetersenTarget (rowMap (layout q) v) = read PetersenCycleFive.target v := by decide

private theorem nonconst : ¬ ∃ b, read PetersenCycleFive.target = fun _ => b := by
  rintro ⟨b,h⟩
  have u := congrFun h 0
  have v := congrFun h 3
  change false = b at u
  change true = b at v
  simp_all

theorem binary_lower {k W} (src : Run base k W) (out : Av W PetersenTarget) : 14 ≤ k := by
  have small : NoAtMost (inputs 5) PetersenCycleFive.target 6 := by
    have h : inputs 5 = PetersenCycleFive.input := by decide
    rw [h]
    exact PetersenCycleFive.no_six_gates
  apply pair_lift (n := 5) PetersenCycleFive.target nonconst small (d := 5) _ src out
  intro i j ne
  obtain ⟨left,right⟩ := lookup i j ne
  exact ⟨layout (choice i j),left,right,le_of_eq (nfixed _).symm,funext (row_check _)⟩

theorem public_lower (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) :
    14 ≤ C.size := by
  obtain ⟨W,r,o⟩ := signed_realization C σ u fan
  rw [funext computes] at o
  exact (binary_lower r o).trans (List.length_filter_le ..)

#print axioms binary_lower
#print axioms public_lower

end PetersenFourteen
