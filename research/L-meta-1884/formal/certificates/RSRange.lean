import RSWord
import PetersenRootOrbit
import PetersenSignedDemand
import PetersenPackedRoot

open PetersenWordCost PetersenLayerCheck PetersenVerifiedGroup PetersenFrontierSymmetry
open PetersenSignedBridge PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Root17
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem raw_eq : inputs 10 = primary := by decide +kernel

theorem tgt_eq : graphWord E = tgt := by
  apply read_inj
  unfold graphWord graphTarget
  rw [read_pack]
  funext i
  revert i
  decide +kernel

def probes : List (Nat × Nat) := [(2,3),(1,3),(2,6),(4,12),(8,24),(1,33),(2,66),(4,132),(8,264),(16,528)]

theorem no16_of_closure (done : Blocked tgt 16 primary) : NoAtMost (inputs 10) tgt 16 := by
  rw [raw_eq]
  apply PetersenSignedDemand.lower (by decide) _ (by rfl) _ probes (by decide +kernel) done
  · intro a ha
    unfold primary at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · constructor
    · intro eq
      have h := congrFun eq (3 : Fin 1024)
      change true = false at h; contradiction
    · intro eq
      have h := congrFun eq (0 : Fin 1024)
      change false = true at h; contradiction

theorem origin_eq : PetersenPackedRoot.target = tgt := by
  apply read_inj
  rw [PetersenPackedRoot.target,read_pack]
  funext i
  revert i
  decide +kernel

theorem public_of_closure (done : Blocked tgt 16 primary) (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (fan : FanInTwo C) (computes : ∀ x : PInput,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 17 ≤ C.size := by
  have low := no16_of_closure done
  rw [←origin_eq] at low
  obtain ⟨W,run,out⟩ := signed_realization C σ u fan
  rw [funext computes] at out
  by_contra small
  exact PetersenPackedRoot.signed_of_words low _ (by
    have le : (C.gates.filter paid).length ≤ C.gates.length := List.length_filter_le ..
    change ¬ 17 ≤ C.gates.length at small
    omega) W run out

#print axioms public_of_closure
end Root17
