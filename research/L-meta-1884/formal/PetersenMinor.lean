import PetersenTracePin
import PetersenWordCost

open PetersenSignedBridge PetersenFrontier PetersenWordCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenMinor
noncomputable local instance {X : Type} : DecidableEq (Func X) := Classical.decEq _
noncomputable local instance {X Y : Type} (r : Y → X) : DecidablePred (PetersenTracePin.constant r) :=
  Classical.decPred _

private theorem polarity {X : Type} {u v : Func X} (h : negRelated u v) :
    (∃ s, u = PetersenTracePin.signed s v) ∧ (∃ s, v = PetersenTracePin.signed s u) := by
  rcases h with rfl | rfl
  · exact ⟨⟨false,rfl⟩,⟨false,rfl⟩⟩
  · refine ⟨⟨true,rfl⟩,⟨true,?_⟩⟩
    funext x
    simp [PetersenTracePin.signed,PetersenFrontier.flip]

theorem keyedSigned {X : Type} (key : Func X → Func X) (sgn : ∀ f, negRelated (key f) f)
    {a b o} (h : keyedGate key a b o) : PetersenTracePin.gate a b o := by
  obtain ⟨u,v,op,rfl,rfl,rfl,_⟩ := h
  obtain ⟨sa,ea⟩ := (polarity (sgn u)).2
  obtain ⟨sb,eb⟩ := (polarity (sgn v)).2
  obtain ⟨so,eo⟩ := (polarity (sgn (bin op u v))).1
  refine ⟨op,sa,sb,so,?_⟩
  rw [← ea,← eb]
  exact eo

theorem trace_weaken {α : Type} [DecidableEq α] {g h : α → α → α → Prop}
    {I W m c} (tr : Trace g I m c W) (en : ∀ a b o, g a b o → h a b o) :
    Trace h I m c W := by
  induction tr with
  | start => exact Trace.start
  | step _ hab ho g ih => exact Trace.step ih hab ho (en _ _ _ g)

def rowMap {n : Nat} (cols : Fin 10 → Bool ⊕ Fin n) (row : Fin (2^n)) : PInput :=
  fun i => (cols i).elim id (fun j => row.val.testBit j.val)

theorem coordinate {n} (i : Fin n) :
    (fun x : Fin (2^n) => x.val.testBit i.val) ∈ (inputs n).map read := by
  apply List.mem_map.mpr
  refine ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,read_pack _⟩

theorem fix_cover {n} (cols : Fin 10 → Bool ⊕ Fin n) (f : Func PInput) (hf : f ∈ base.toFinset) :
    Av ((inputs n).map read) (f ∘ rowMap cols) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hf)
  change Av _ (fun row : Fin (2^n) => (cols i).elim id (fun j => row.val.testBit j.val))
  cases h : cols i with
  | inl b => cases b <;> first | exact Av.zero | exact Av.one
  | inr j => exact Av.wire (coordinate j)

def fixed {n} (cols : Fin 10 → Bool ⊕ Fin n) : Finset (Fin 10) :=
  Finset.univ.filter fun i => (cols i).isLeft

theorem manyFixed {n} (cols : Fin 10 → Bool ⊕ Fin n) :
    (fixed cols).card ≤ (base.toFinset.filter (PetersenTracePin.constant (rowMap cols))).card := by
  have inj : Function.Injective vertex := by
    intro i j e
    have eq := congrFun e (fun h => decide (h=i))
    simpa [vertex,eq_comm] using eq
  rw [← Finset.card_image_of_injective (fixed cols) inj]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
  refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩),?_⟩
  have l := (Finset.mem_filter.mp hi).2
  cases e : cols i with
  | inl b =>
    refine ⟨b,?_⟩
    funext r
    simp [vertex,rowMap,e]
  | inr j => simp [e] at l

/-- One checked exclusion on a restricted target transfers to every original signed circuit.
    Distinct primary signals becoming constant each supply a separate gate in the lower bound. -/
theorem root_lower {n K : Nat} (cols : Fin 10 → Bool ⊕ Fin n) (target : BitVec (2^n))
    (agrees : PetersenTarget ∘ rowMap cols = read target)
    (nonconstant : ¬ ∃ b, read target = fun _ => b)
    (lower : NoAtMost (inputs n) target K) {k W}
    (src : Run base k W) (out : Av W PetersenTarget) : (K+1) + (fixed cols).card ≤ k := by
  obtain ⟨m,hm,c,t,_⟩ := petersen_signed_frontier src out
  have tr := trace_weaken t (fun _ _ _ g => keyedSigned _ (signedSign zeroInput) g.2)
  have nc : ¬ PetersenTracePin.constant (rowMap cols) PetersenTarget := by
    simpa [PetersenTracePin.constant,agrees] using nonconstant
  have bound := PetersenTracePin.prune_suffix (rowMap cols) tr (Run.start (init := (inputs n).map read))
    (fix_cover cols) nc (lower := K+1) (by
      intro j V r o
      rw [agrees] at o
      by_contra h
      exact lower j (by omega) V r o)
  have le := manyFixed cols
  omega

/-- The public evaluator inherits each restricted lower bound, for all rewirings and unary choices. -/
theorem public_lower {n K : Nat} (cols : Fin 10 → Bool ⊕ Fin n) (target : BitVec (2^n))
    (agrees : PetersenTarget ∘ rowMap cols = read target) (nonconstant : ¬ ∃ b, read target = fun _ => b)
    (lower : NoAtMost (inputs n) target K) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (allowed : FanInTwo C) (computes : ∀ x : PInput,
        C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) :
    (K+1) + (fixed cols).card ≤ C.size := by
  obtain ⟨W,r,o⟩ := signed_realization C σ u allowed
  rw [funext computes] at o
  exact (root_lower cols target agrees nonconstant lower r o).trans (List.length_filter_le ..)

end PetersenMinor
