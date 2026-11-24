import PetersenPhysicalBoundary

open PetersenSignedBridge
namespace PetersenPinDrop
variable {Ω Θ : Type}

/-- A wire either ignores the selected coordinate or is constant on the chosen slice. -/
def Simple (lo hi : Θ → Ω) (f : Func Ω) : Prop :=
  f ∘ lo = f ∘ hi ∨ ∃ b : Bool, f ∘ lo = fun _ => b

private theorem wk {W : List (Func Θ)} {f g : Func Θ} (h : Av W f) : Av (g::W) f := by
  induction h with
  | wire e => exact Av.wire (List.mem_cons_of_mem _ e)
  | zero => exact Av.zero
  | one => exact Av.one
  | neg _ ih => exact Av.neg ih

private theorem constAv (W : List (Func Θ)) (b : Bool) : Av W (fun _ => b) := by
  cases b <;> first | exact .zero | exact .one

private theorem extendAv (lo : Θ → Ω) {W : List (Func Ω)} {V : List (Func Θ)}
    (h : ∀ f ∈ W, Av V (f ∘ lo)) {f} (a : Av W f) : Av V (f ∘ lo) := by
  induction a with
  | wire m => exact h _ m
  | zero => exact .zero
  | one => exact .one
  | neg _ ih => exact .neg ih

private theorem extendSimple (lo hi : Θ → Ω) {W : List (Func Ω)}
    (h : ∀ f ∈ W, Simple lo hi f) {f} (a : Av W f) : Simple lo hi f := by
  induction a with
  | wire m => exact h _ m
  | zero => exact Or.inl rfl
  | one => exact Or.inl rfl
  | @neg f a ih =>
    rcases ih with same | ⟨b,hb⟩
    · exact Or.inl (congrArg (fun f : Func Θ => fun x => !(f x)) same)
    · exact Or.inr ⟨!b,congrArg (fun f : Func Θ => fun x => !(f x)) hb⟩

private def op (kind : Bool) (a b : Func Ω) : Func Ω := fun x => if kind then a x || b x else a x && b x

private theorem appendOp {J V : List (Func Θ)} {j} (r : Run J j V) {a b}
    (ha : Av V a) (hb : Av V b) (kind : Bool) : Run J (j+1) (op kind a b :: V) := by
  cases kind
  · exact .and r ha hb
  · exact .or r ha hb

private theorem simplify {V : List (Func Θ)} {a b : Func Θ} (ha : Av V a) (hb : Av V b)
    (h : (∃ v, a = fun _ => v) ∨ (∃ v, b = fun _ => v)) (kind : Bool) : Av V (op kind a b) := by
  have transfer {c d : Func Θ} (ok : Av V c) (eq : ∀ x, c x = d x) : Av V d := (funext eq) ▸ ok
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases kind <;> cases v
    · exact transfer (constAv V false) (by intro x; simp [op])
    · exact transfer hb (by intro x; simp [op])
    · exact transfer hb (by intro x; simp [op])
    · exact transfer (constAv V true) (by intro x; simp [op])
  · cases kind <;> cases v
    · exact transfer (constAv V false) (by intro x; simp [op])
    · exact transfer ha (by intro x; simp [op])
    · exact transfer ha (by intro x; simp [op])
    · exact transfer (constAv V true) (by intro x; simp [op])

private def Compressed (lo hi : Θ → Ω) (J : List (Func Θ)) (k : Nat) (W : List (Func Ω)) : Prop :=
  ∃ j V, j ≤ k ∧ Run J j V ∧ (∀ f ∈ W, Av V (f ∘ lo)) ∧ (j < k ∨ ∀ f ∈ W, Simple lo hi f)

private theorem step {lo hi : Θ → Ω} {J : List (Func Θ)} {k W}
    (h : Compressed lo hi J k W) {a b} (ha : Av W a) (hb : Av W b) (kind : Bool) :
    Compressed lo hi J (k+1) (op kind a b::W) := by
  obtain ⟨j,V,hj,r,available,stats⟩ := h
  let a' := a ∘ lo
  let b' := b ∘ lo
  have aa : Av V a' := extendAv lo available ha
  have ab : Av V b' := extendAv lo available hb
  by_cases constant : (∃ v, a' = fun _ => v) ∨ (∃ v, b' = fun _ => v)
  · refine ⟨j,V,by omega,r,?_,Or.inl (by omega)⟩
    intro f hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact simplify aa ab constant kind
    · exact available _ hm
  · refine ⟨j+1,op kind a' b'::V,by omega,appendOp r aa ab kind,?_,?_⟩
    · intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Av.wire (by exact List.mem_cons_self (a := op kind a' b') (l := V))
      · exact wk (available _ hm)
    · rcases stats with smaller | shapes
      · exact Or.inl (by omega)
      · apply Or.inr
        intro f hm
        rcases List.mem_cons.mp hm with rfl | hm
        · obtain hA | cA := extendSimple lo hi shapes ha
          · obtain hB | cB := extendSimple lo hi shapes hb
            · exact Or.inl (congrArg₂ (op kind) hA hB)
            · exact False.elim (constant (Or.inr cB))
          · exact False.elim (constant (Or.inl cA))
        · exact shapes _ hm

/-- If the output depends on the pinned coordinate and is still nonconstant on that slice,
    a signed run specializes to a strictly shorter signed run. The maps also cover input reindexing. -/
theorem shorten {lo hi : Θ → Ω} {I : List (Func Ω)} {J : List (Func Θ)}
    (hI : ∀ f ∈ I, Av J (f ∘ lo)) (shapes : ∀ f ∈ I, Simple lo hi f)
    {k W} (r : Run I k W) {f} (hf : Av W f) (complex : ¬Simple lo hi f) :
    ∃ j < k, ∃ V, Run J j V ∧ Av V (f ∘ lo) := by
  have c : Compressed lo hi J k W := by
    clear hf complex
    induction r with
    | start => exact ⟨0,J,by omega,.start,hI,Or.inr shapes⟩
    | and _ ha hb ih => exact step ih ha hb false
    | or _ ha hb ih => exact step ih ha hb true
  obtain ⟨j,V,_,rr,available,h⟩ := c
  refine ⟨j,?_,V,rr,extendAv lo available hf⟩
  rcases h with hj | sh
  · exact hj
  · exact False.elim (complex (extendSimple lo hi sh hf))

end PetersenPinDrop
