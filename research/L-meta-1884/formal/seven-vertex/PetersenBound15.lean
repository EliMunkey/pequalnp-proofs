import D9Closing
import PetersenPairMinor
open PetersenMinor PetersenPairMinor PetersenSignedBridge PetersenWordCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PetersenBound15
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def layout : Fin 30 → Fin 10 → Bool ⊕ Fin 7 := ![![.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inl false,.inr 6,.inl false,.inl false],![.inr 4,.inr 0,.inr 1,.inr 2,.inr 3,.inl false,.inr 5,.inl false,.inr 6,.inl false],![.inr 4,.inr 0,.inr 5,.inl false,.inr 3,.inl false,.inr 1,.inr 6,.inl false,.inr 2],![.inr 1,.inr 0,.inr 4,.inl false,.inl false,.inr 2,.inr 5,.inr 3,.inr 6,.inl false],![.inr 0,.inr 1,.inl false,.inl false,.inr 5,.inr 4,.inr 2,.inl false,.inr 3,.inr 6],![.inr 1,.inl false,.inl false,.inr 5,.inr 0,.inr 2,.inl false,.inr 3,.inr 6,.inr 4],![.inl false,.inr 1,.inr 0,.inr 4,.inl false,.inl false,.inr 2,.inr 5,.inr 3,.inr 6],![.inl false,.inl false,.inr 1,.inr 0,.inr 5,.inr 3,.inl false,.inr 2,.inr 4,.inr 6],![.inr 0,.inr 4,.inr 3,.inr 2,.inr 1,.inr 5,.inl false,.inl false,.inr 6,.inl false],![.inr 1,.inr 0,.inr 4,.inr 3,.inr 2,.inl false,.inr 5,.inl false,.inl false,.inr 6],![.inr 3,.inr 4,.inr 0,.inr 1,.inr 2,.inl false,.inl false,.inr 5,.inl false,.inr 6],![.inr 5,.inr 0,.inr 4,.inr 3,.inl false,.inr 6,.inr 1,.inl false,.inr 2,.inl false],![.inr 3,.inr 4,.inr 0,.inr 5,.inl false,.inr 2,.inl false,.inr 1,.inr 6,.inl false],![.inr 0,.inr 4,.inr 3,.inl false,.inr 5,.inr 1,.inl false,.inr 2,.inl false,.inr 6],![.inr 4,.inr 0,.inr 1,.inl false,.inl false,.inr 3,.inr 5,.inr 2,.inl false,.inr 6],![.inr 0,.inr 5,.inl false,.inr 3,.inr 4,.inr 1,.inr 6,.inl false,.inr 2,.inl false],![.inr 4,.inr 3,.inl false,.inr 5,.inr 0,.inl false,.inr 2,.inl false,.inr 6,.inr 1],![.inr 0,.inr 4,.inl false,.inl false,.inr 1,.inr 5,.inr 3,.inr 6,.inl false,.inr 2],![.inr 4,.inr 3,.inl false,.inl false,.inl false,.inr 0,.inr 2,.inr 5,.inr 1,.inr 6],![.inr 3,.inl false,.inr 5,.inr 0,.inr 4,.inr 2,.inl false,.inr 6,.inr 1,.inl false],![.inr 5,.inl false,.inr 3,.inr 4,.inr 0,.inr 6,.inl false,.inr 2,.inl false,.inr 1],![.inr 4,.inl false,.inl false,.inr 1,.inr 0,.inr 3,.inr 6,.inl false,.inr 2,.inr 5],![.inr 4,.inl false,.inl false,.inl false,.inr 3,.inr 0,.inr 6,.inr 1,.inr 5,.inr 2],![.inl false,.inr 5,.inr 0,.inr 4,.inr 3,.inl false,.inr 6,.inr 1,.inl false,.inr 2],![.inl false,.inr 3,.inr 4,.inr 0,.inr 5,.inl false,.inr 2,.inl false,.inr 1,.inr 6],![.inl false,.inr 5,.inr 0,.inr 1,.inl false,.inr 3,.inr 6,.inr 4,.inr 2,.inl false],![.inl false,.inr 4,.inr 3,.inl false,.inl false,.inr 6,.inr 0,.inr 2,.inr 5,.inr 1],![.inl false,.inl false,.inr 5,.inr 0,.inr 1,.inl false,.inr 3,.inr 6,.inr 4,.inr 2],![.inl false,.inl false,.inr 4,.inr 3,.inl false,.inr 1,.inr 6,.inr 0,.inr 2,.inr 5],![.inl false,.inl false,.inl false,.inr 4,.inr 3,.inr 5,.inr 1,.inr 6,.inr 0,.inr 2]]
private def choice : Fin 10 → Fin 10 → Fin 30 := ![![0,7,29,26,6,6,7,24,23,25],![7,0,5,22,28,27,5,21,20,19],![29,5,0,4,18,16,5,4,17,15],![26,22,4,0,3,2,13,4,2,3],![6,28,18,3,0,6,12,11,14,3],![6,27,16,2,6,0,10,1,2,1],![7,5,5,13,12,10,0,8,0,0],![24,21,4,4,11,1,8,0,9,1],![23,20,17,2,14,2,0,9,0,0],![25,19,15,3,3,1,0,1,0,0]]
private theorem covers : ∀ i j : Fin 10, i ≠ j →
    (layout (choice i j) i).isLeft ∧ (layout (choice i j) j).isLeft := by decide +kernel
private theorem nfixed : ∀ q : Fin 30, (fixed (layout q)).card = 3 := by decide +kernel
private theorem tables : ∀ (q : Fin 30) (v : Fin 128),
    PetersenTarget (rowMap (layout q) v) = read Deleted191Cost9.tgt v := by decide +kernel
private theorem nonconst : ¬∃ b, read Deleted191Cost9.tgt = fun _ => b := by
  rintro ⟨b,h⟩
  have e := congrFun h 0
  have f := congrFun h 3
  change false = b at e
  change true = b at f
  simp_all
theorem binary_lower {k W} (src : Run base k W) (out : Av W PetersenTarget) : 15 ≤ k := by
  have small : NoAtMost (inputs 7) Deleted191Cost9.tgt 9 := Deleted191Cost9.bound
  apply pair_lift (n := 7) Deleted191Cost9.tgt nonconst small (d := 3) _ src out
  intro i j h
  obtain ⟨a,b⟩ := covers i j h
  exact ⟨layout (choice i j),a,b,le_of_eq (nfixed _).symm,funext (tables _)⟩
theorem public_lower (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 15 ≤ C.size := by
  obtain ⟨W,r,o⟩ := signed_realization C σ u fan
  rw [funext computes] at o
  exact (binary_lower r o).trans (List.length_filter_le ..)
#print axioms public_lower
end PetersenBound15
