import PetersenPinDrop

open PetersenSignedBridge PetersenPinDrop
namespace PetersenSingleton
variable {Ω : Type}

/-- The new first rail is a fresh independent input. All earlier rails ignore it. -/
def extend (I : List (Func Ω)) : List (Func (Bool × Ω)) :=
  Prod.fst :: I.map (fun f p => f p.2)

def withSingleton (f : Func Ω) : Func (Bool × Ω) := fun x => x.1 || f x.2

def Realized (I : List (Func Ω)) (f : Func Ω) (k : Nat) : Prop :=
  ∃ W, Run I k W ∧ Av W f

/-- Adjoining an independent singleton OR to a nonconstant target costs at least one extra gate. -/
theorem lower {I : List (Func Ω)} {f : Func Ω} (no : ∃ x, f x = false) (yes : ∃ x, f x = true)
    {k} (h : Realized (extend I) (withSingleton f) k) : ∃ j < k, Realized I f j := by
  let lo (x : Ω) := (false,x)
  let hi (x : Ω) := (true,x)
  have cov g (hg : g ∈ extend I) : Av I (g ∘ lo) := by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Av.zero
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg;exact Av.wire hu
  have shapes g (hg : g ∈ extend I) : Simple lo hi g := by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Or.inr ⟨false,rfl⟩
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg;exact Or.inl rfl
  have nontrivial : ¬ Simple lo hi (withSingleton f) := by
    obtain ⟨n,hn⟩ := no; obtain ⟨y,hy⟩ := yes
    rintro (stable | ⟨b,flat⟩)
    · have h := congrFun stable n;simp [lo,hi,withSingleton,hn] at h
    · have a := congrFun flat n;have d := congrFun flat y;simp [lo,withSingleton,hn] at a;simp [lo,withSingleton,hy] at d;cases b <;> simp_all
  obtain ⟨W,r,v⟩ := h
  obtain ⟨j,hj,V,s,o⟩ := shorten cov shapes r v nontrivial
  exact ⟨j,hj,V,s,by simpa [lo,withSingleton,Function.comp_def] using o⟩

private theorem extendRun {I W : List (Func Ω)} {k} (r : Run I k W) :
    ∃ V, Run (extend I) k V ∧ Prod.fst ∈ V ∧ ∀ f ∈ W, (fun p : Bool × Ω => f p.2) ∈ V := by
  have av {S : List (Func Ω)} {T : List (Func (Bool × Ω))} (cov : ∀ f ∈ S, (fun p : Bool × Ω => f p.2) ∈ T)
      {f} (a : Av S f) : Av T (fun p : Bool × Ω => f p.2) := by
    induction a with
    | wire hf => exact .wire (cov _ hf)
    | zero => exact .zero
    | one => exact .one
    | neg _ ih => exact .neg ih
  induction r with
  | start => exact ⟨_,.start,List.mem_cons_self ..,fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)⟩
  | @and k W a b r ha hb ih =>
    obtain ⟨V,s,keep,cov⟩ := ih
    refine ⟨_,.and s (av cov ha) (av cov hb),List.mem_cons_of_mem _ keep,?_⟩
    intro f h;rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (cov _ h)
  | @or k W a b r ha hb ih =>
    obtain ⟨V,s,keep,cov⟩ := ih
    refine ⟨_,.or s (av cov ha) (av cov hb),List.mem_cons_of_mem _ keep,?_⟩
    intro f h;rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (cov _ h)

theorem upper {I : List (Func Ω)} {f : Func Ω} {k} (h : Realized I f k) :
    Realized (extend I) (withSingleton f) (k+1) := by
  obtain ⟨W,r,a⟩ := h
  obtain ⟨V,s,haveInput,cov⟩ := extendRun r
  have available : Av V (fun p : Bool × Ω => f p.2) := by
    induction a with
    | wire m => exact .wire (cov _ m)
    | zero => exact .zero
    | one => exact .one
    | neg _ ih => exact .neg ih
  exact ⟨_,.or s (.wire haveInput) available,.wire (List.mem_cons_self ..)⟩

/-- The recorded size is achieved and every smaller size is excluded. -/
def Minimum (I : List (Func Ω)) (f : Func Ω) (k : Nat) : Prop :=
  Realized I f k ∧ ∀ j < k, ¬ Realized I f j

theorem minimum_extend {I : List (Func Ω)} {f : Func Ω} {k : Nat}
    (no : ∃ x, f x = false) (yes : ∃ x, f x = true) (h : Minimum I f k) :
    Minimum (extend I) (withSingleton f) (k+1) := by
  refine ⟨upper h.1,?_⟩
  intro j hj circuit
  obtain ⟨a,ha,r⟩ := lower no yes circuit
  exact h.2 a (by omega) r

/-- A product of `n+1` Boolean inputs. -/
def Cube : Nat → Type
  | 0 => Bool
  | n+1 => Bool × Cube n

def primaries : (n : Nat) → List (Func (Cube n))
  | 0 => [id]
  | n+1 => extend (primaries n)

def disjunction : (n : Nat) → Func (Cube n)
  | 0 => id
  | n+1 => withSingleton (disjunction n)

private theorem both_values : ∀ n, (∃ x, disjunction n x = false) ∧ (∃ x, disjunction n x = true) := by
  intro n;induction n with
  | zero => exact ⟨⟨false,rfl⟩,⟨true,rfl⟩⟩
  | succ n ih =>
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := ih
    exact ⟨⟨(false,x),by simpa [disjunction,withSingleton] using hx⟩,
      ⟨(true,y),by simp [disjunction,withSingleton]⟩⟩

/-- Pure OR on exactly `n+1` independent variables has signed binary circuit size exactly `n`. -/
theorem minimum_disjunction : ∀ n, Minimum (primaries n) (disjunction n) n := by
  intro n;induction n with
  | zero => exact ⟨⟨_,Run.start,Av.wire (List.mem_cons_self ..)⟩,fun j h => by omega⟩
  | succ n ih => exact minimum_extend (both_values n).1 (both_values n).2 ih

#print axioms minimum_extend
#print axioms minimum_disjunction
end PetersenSingleton
