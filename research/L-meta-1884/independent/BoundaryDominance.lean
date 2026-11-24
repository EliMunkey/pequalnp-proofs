import Std

namespace BoundaryDominance

/-- On a positive boundary row a replacement may increase a value. On a negative row it may decrease it. -/
def Better (label old replacement : Bool) : Prop := old = label → replacement = label

instance (y a b : Bool) : Decidable (Better y a b) := by unfold Better; infer_instance

theorem better_and : ∀ y a a' b b' : Bool, Better y a a' → Better y b b' →
    Better y (a && b) (a' && b') := by decide

theorem better_or : ∀ y a a' b b' : Bool, Better y a a' → Better y b b' →
    Better y (a || b) (a' || b') := by decide

inductive WireExpr (α : Type) where
  | input (v : α)
  | conj (a b : WireExpr α)
  | disj (a b : WireExpr α)

def WireExpr.eval {α} (ρ : α → Bool) : WireExpr α → Bool
  | .input v => ρ v
  | .conj a b => a.eval ρ && b.eval ρ
  | .disj a b => a.eval ρ || b.eval ρ

/-- Every subsequent wire in a physical AND/OR circuit respects target-directed dominance. -/
theorem WireExpr.eval_better {α} (e : WireExpr α) (label : Bool) (ρ σ : α → Bool)
    (h : ∀ i, Better label (ρ i) (σ i)) : Better label (e.eval ρ) (e.eval σ) := by
  induction e with
  | input v => exact h v
  | conj _ _ a b => exact better_and _ _ _ _ _ a b
  | disj _ _ a b => exact better_or _ _ _ _ _ a b

/-- No correctly classified boundary row can change its label when the suffix reads better rails. -/
theorem preserves_output {α R} (e : WireExpr α) (label : R → Bool) (old new : R → α → Bool)
    (h : ∀ r i, Better (label r) (old r i) (new r i))
    (h₀ : ∀ r, e.eval (old r) = label r) : ∀ r, e.eval (new r) = label r := by
  intro r
  exact e.eval_better (label r) (old r) (new r) (h r) (h₀ r)

/-- A correct bit receives one point independently of its Boolean polarity. -/
def point (y a : Bool) : Nat := if a == y then 1 else 0

theorem score_nonworse : ∀ y a b : Bool, Better y a b → point y a ≤ point y b := by decide

theorem score_improves : ∀ y a b : Bool, Better y a b → a ≠ b → point y a < point y b := by decide

end BoundaryDominance
