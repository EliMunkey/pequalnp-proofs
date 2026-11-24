import PetersenMinor
import PetersenPathFour

open PetersenSignedBridge PetersenMinor PetersenWordCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PetersenBounds

def pathCols : Fin 10 → Bool ⊕ Fin 4 :=
  ![.inr 0,.inr 1,.inr 2,.inr 3,.inl false,.inl false,.inl false,.inl false,.inl false,.inl false]

private theorem pathRows : PetersenTarget ∘ rowMap pathCols = read PetersenPathFour.target := by
  funext x
  revert x
  decide

private theorem pathNonconstant : ¬ ∃ b, read PetersenPathFour.target = fun _ => b := by
  rintro ⟨b,h⟩
  have u := congrFun h 0
  have v := congrFun h 3
  change false = b at u
  change true = b at v
  simp_all

theorem at_least_ten (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (allowed : FanInTwo C) (computes : ∀ x : PInput,
        C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = PetersenTarget x) : 10 ≤ C.size := by
  have no3 : NoAtMost (inputs 4) PetersenPathFour.target 3 := by
    have eq : inputs 4 = PetersenPathFour.input := by decide
    rw [eq]
    exact PetersenPathFour.no_three_gates
  have h := public_lower pathCols _ pathRows pathNonconstant no3 C σ u allowed computes
  have count : (fixed pathCols).card = 6 := by decide
  omega

def witness : Circuit :=
  ⟨[⟨.or,[1,4]⟩,
    ⟨.or,[11,5]⟩,
    ⟨.and,[0,12]⟩,
    ⟨.or,[2,6]⟩,
    ⟨.and,[1,14]⟩,
    ⟨.or,[2,4]⟩,
    ⟨.or,[16,8]⟩,
    ⟨.and,[3,17]⟩,
    ⟨.or,[2,5]⟩,
    ⟨.or,[19,9]⟩,
    ⟨.and,[7,20]⟩,
    ⟨.or,[5,6]⟩,
    ⟨.and,[8,22]⟩,
    ⟨.or,[4,6]⟩,
    ⟨.and,[9,24]⟩,
    ⟨.or,[13,15]⟩,
    ⟨.or,[26,18]⟩,
    ⟨.or,[27,21]⟩,
    ⟨.or,[28,23]⟩,
    ⟨.or,[29,25]⟩],30⟩

private theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;>
    simp [Set.mem_insert_iff,Set.mem_singleton_iff]

theorem twenty_works : FanInTwo witness ∧ witness.size = 20 ∧
    ∀ x : PInput, witness.eval (List.ofFn x ++ [false]) = PetersenTarget x := by
  refine ⟨fan,rfl,?_⟩
  intro x
  have coordinates : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  rw [coordinates]
  simp only [Circuit.eval, Circuit.wires, witness, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_succ,
    List.getD_cons_zero, GateOp.eval, List.all_cons, List.all_nil, List.any_cons,
    List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  simp only [PetersenTarget, Bool.and_or_distrib_left]
  ac_rfl

#print axioms at_least_ten
#print axioms twenty_works
end PetersenBounds
