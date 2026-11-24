import PetersenPhysicalWords
open PetersenSignedBridge PetersenWordCost PetersenPhysicalWords
namespace PetersenMonotoneSample

def Rises {X : Type} (rel : X → X → Prop) (f : X → Bool) : Prop :=
  ∀ x y, rel x y → f x=true → f y=true

def Represents {w : Nat} {X : Type} (row : Fin w→X) (rel : X→X→Prop)
    (W : List (Func X)) (a : BitVec w) : Prop :=
  ∃ f, Av W f ∧ Rises rel f ∧ read a=f ∘ row

private theorem keep {X : Type} {W : List (Func X)} {f g} (av : Av W f) : Av (g::W) f := by
  induction av with
  | wire h => exact .wire (List.mem_cons_of_mem _ h)
  | zero => exact .zero
  | one => exact .one
  | neg _ ih => exact .neg ih

def opFun {X : Type} (op : Bool) (f g : Func X) : Func X :=
  fun x => if op then f x || g x else f x && g x

private theorem build {X : Type} {init W : List (Func X)} {k f g} (r : Run init k W)
    (af : Av W f) (ag : Av W g) (op : Bool) : Run init (k+1) (opFun op f g :: W) := by
  cases op
  · exact .and r af ag
  · exact .or r af ag

private theorem rises_op {X : Type} {rel : X→X→Prop} {f g : Func X}
    (a : Rises rel f) (b : Rises rel g) (op : Bool) : Rises rel (opFun op f g) := by
  intro x y r h
  have ax := a x y r; have bx := b x y r
  cases op <;> simp [opFun] at h ⊢ <;> tauto

/-- Lift a positive program on sampled rows back to monotone functions on all rows. -/
theorem lift {w : Nat} {X : Type} (row : Fin w→X) (rel : X→X→Prop)
    {init : List (Func X)} {I S : List (BitVec w)} {k}
    (base : ∀ a∈I, Represents row rel init a) (p : Positive I k S) :
    ∃ W, Run init k W ∧ ∀ a∈S, Represents row rel W a := by
  induction p with
  | start => exact ⟨_,Run.start,base⟩
  | @add k W a b op _ ha hb ih =>
    obtain ⟨V,pr,ok⟩ := ih
    obtain ⟨f,af,mf,ef⟩ := ok a ha
    obtain ⟨g,ag,mg,eg⟩ := ok b hb
    refine ⟨_,build pr af ag op,?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl|mem
    · refine ⟨_,Av.wire (List.mem_cons_self ..),rises_op mf mg op,?_⟩
      funext i; have aeq := congrFun ef i; have beq := congrFun eg i
      cases op <;> simpa [opFun,PetersenWordCost.gate,PetersenWordCost.read,Function.comp_def] using
        (by first | exact congrArg₂ Bool.and aeq beq | exact congrArg₂ Bool.or aeq beq)
    · obtain ⟨f,af,mf,ef⟩ := ok v mem
      exact ⟨f,keep af,mf,ef⟩
end PetersenMonotoneSample
