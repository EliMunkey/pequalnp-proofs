import PetersenPhysicalDemand
import PetersenPhysicalSearch

open PetersenSignedBridge PetersenWordCost PetersenFrontierSearch
namespace PetersenPackedRoot

def row (x : Fin 1024) : PInput := PhysicalBoundary.word x.val
def target : BitVec 1024 := pack (PetersenTarget ∘ row)

private theorem sampleAv {X Y : Type} (e : Y → X) {W : List (Func X)} {f : Func X}
    (h : Av W f) : Av (W.map (· ∘ e)) (f ∘ e) := by
  induction h with
  | wire he => exact Av.wire (List.mem_map.mpr ⟨_,he,rfl⟩)
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem sampleRun {X Y : Type} (e : Y → X) {I W : List (Func X)} {k}
    (r : Run I k W) : Run (I.map (· ∘ e)) k (W.map (· ∘ e)) := by
  induction r with
  | start => exact Run.start
  | and _ ha hb ih => exact Run.and ih (sampleAv e ha) (sampleAv e hb)
  | or _ ha hb ih => exact Run.or ih (sampleAv e ha) (sampleAv e hb)

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 2048 in
private theorem inputs_eq : base.map (· ∘ row) = (inputs 10).map read := by
  simp only [base,inputs,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact (read_pack (fun x : Fin 1024 => x.val.testBit i.val)).symm

theorem signed_of_words {K : Nat} (h : NoAtMost (inputs 10) target K) :
    ∀ k ≤ K, ∀ W, Run base k W → ¬ Av W PetersenTarget := by
  intro k hk W r o
  have rr := sampleRun row r
  rw [inputs_eq] at rr
  exact h _ hk _ rr (by simpa only [target,read_pack] using sampleAv row o)

open PetersenPhysicalWords PetersenPhysicalSearch

theorem physical_of_words (h : Blocked input pivot PetersenPhysicalWords.target 18 input) :
    ∀ W, Direct rails 18 W → PetersenTarget ∉ W := by
  intro W r o
  obtain ⟨m,hm,c,t,_⟩ := PetersenPhysicalDemand.all_ten r o
  exact h m hm c (to_tail t)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem original_of_word_exclusions (h₁ : NoAtMost (inputs 10) PetersenPackedRoot.target 17)
    (h₂ : Blocked input pivot PetersenPhysicalWords.target 18 input) :
    ∀ (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool), FanInTwo C → C.size ≤ 18 →
      ∃ x : PInput, C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ PetersenTarget x :=
  L_meta_1884_of_exclusions (signed_of_words h₁) (physical_of_words h₂)
#print axioms original_of_word_exclusions
end PetersenPackedRoot
