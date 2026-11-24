import PetersenFirstUse

open PetersenSignedBridge PetersenFrontier PetersenWordCost PetersenMinor PetersenFirstUse
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenPairMinor

noncomputable local instance {X : Type} : DecidableEq (Func X) := Classical.decEq _
noncomputable local instance {X Y : Type} (r : Y → X) : DecidablePred (PetersenTracePin.constant r) :=
  Classical.decPred _

theorem pair_lift {n K d : Nat} (target : BitVec (2^n))
    (nonconstant : ¬ ∃ b, read target = fun _ => b) (lower : NoAtMost (inputs n) target K)
    (covers : ∀ i j : Fin 10, i ≠ j → ∃ cols : Fin 10 → Bool ⊕ Fin n,
      (cols i).isLeft ∧ (cols j).isLeft ∧ d ≤ (fixed cols).card ∧
      PetersenTarget ∘ rowMap cols = read target) {k W}
    (src : Run base k W) (out : Av W PetersenTarget) : (K+1) + d + 2 ≤ k := by
  obtain ⟨m,hm,c,t,_⟩ := petersen_signed_frontier src out
  have tr := trace_weaken t (fun _ _ _ g => keyedSigned _ (signedSign zeroInput) g.2)
  obtain ⟨i,j,o,rest,charge,ne,g,fresh,tail,eq,_⟩ := first_kept tr
  obtain ⟨cols,hi,hj,size,agrees⟩ := covers i j ne
  let r := rowMap cols
  have fixed_const (l : Fin 10) (h : (cols l).isLeft) : PetersenTracePin.constant r (vertex l) := by
    cases hc : cols l with
    | inl b =>
      refine ⟨b,?_⟩
      funext v
      simp [r,vertex,rowMap,hc]
    | inr b => simp [hc] at h
  have co := PetersenTracePin.constant_gate r g (fixed_const i hi) (fixed_const j hj)
  have cov : ∀ f ∈ insert o base.toFinset, Av ((inputs n).map read) (f ∘ r) := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | old
    · obtain ⟨b,hb⟩ := co
      rw [hb]
      cases b <;> first | exact Av.zero | exact Av.one
    · exact fix_cover cols f old
  have nc : ¬ PetersenTracePin.constant r PetersenTarget := by
    simpa [PetersenTracePin.constant,r,agrees] using nonconstant
  have bound := PetersenTracePin.prune_suffix r tail (Run.start (init := (inputs n).map read))
    cov nc (lower := K+1) (by
      intro l V v h
      change Av V (PetersenTarget ∘ rowMap cols) at h
      rw [agrees] at h
      by_contra low
      exact lower l (by omega) V v h)
  have counted := manyFixed cols
  have inc : ((insert o base.toFinset).filter (PetersenTracePin.constant r)).card =
      (base.toFinset.filter (PetersenTracePin.constant r)).card + 1 := by
    simp [Finset.filter_insert,co,fresh,Finset.card_insert_of_notMem]
  rw [inc] at bound
  change (fixed cols).card ≤ (base.toFinset.filter (PetersenTracePin.constant r)).card at counted
  omega

theorem public_pair_lift {n K d : Nat} (target : BitVec (2^n))
    (nonconstant : ¬ ∃ b, read target = fun _ => b) (lower : NoAtMost (inputs n) target K)
    (covers : ∀ i j : Fin 10, i ≠ j → ∃ cols : Fin 10 → Bool ⊕ Fin n,
      (cols i).isLeft ∧ (cols j).isLeft ∧ d ≤ (fixed cols).card ∧
      PetersenTarget ∘ rowMap cols = read target)
    (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (allowed : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) :
    (K+1) + d + 2 ≤ C.size := by
  obtain ⟨W,r,o⟩ := signed_realization C σ u allowed
  rw [funext computes] at o
  exact (pair_lift target nonconstant lower covers r o).trans (List.length_filter_le ..)

end PetersenPairMinor
