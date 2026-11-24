import PetersenWordCost

namespace PetersenWordCost

def choices {w} (W : List (BitVec w)) := (0 :: W) ++ (0 :: W).map (fun a => ~~~a)

theorem mem_choices {w} {W : List (BitVec w)} {a : BitVec w} : a ∈ choices W ↔ Covered W a := by
  simp only [choices, List.mem_append, List.mem_map, Covered]
  constructor
  · rintro (h | ⟨b,hb,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hb)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨~~~a,h,by simp⟩

def rejectBool {w} (t : BitVec w) : Nat → List (BitVec w) → Bool
  | 0,W => !(choices W).contains t
  | k+1,W => (choices W).all fun a => (choices W).all fun b =>
      rejectBool t k ((a &&& b) :: W) && rejectBool t k ((a ||| b) :: W)

theorem rejectBool_sound {w} (t : BitVec w) : ∀ k W, rejectBool t k W = true → Reject t k W := by
  intro k;induction k with
  | zero =>
    intro W h ha
    have hm := mem_choices.mpr ha
    simpa [rejectBool,hm] using h
  | succ k ih =>
    intro W h a b ha hb op
    have h₁ := List.all_eq_true.mp h a (mem_choices.mpr ha)
    have h₂ := List.all_eq_true.mp h₁ b (mem_choices.mpr hb)
    cases op
    · exact ih _ (Bool.and_eq_true_iff.mp h₂).1
    · exact ih _ (Bool.and_eq_true_iff.mp h₂).2

end PetersenWordCost
